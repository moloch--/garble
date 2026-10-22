// Copyright (c) 2020, The Garble Authors.
// See LICENSE for licensing information.

package literals

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/parser"
	"go/token"
	"go/types"
	mathrand "math/rand"
	"reflect"
	"strconv"
	"unicode/utf8"

	"golang.org/x/tools/go/ast/astutil"
	ah "mvdan.cc/garble/internal/asthelper"
)

// MinSize is the lower bound limit, of the size of string-like literals
// which we will obfuscate. This is needed in order for binary size to stay relatively
// moderate, this also decreases the likelihood for performance slowdowns.
const MinSize = 8

// MaxSize is the upper limit for the per-byte AST obfuscators.
const MaxSize = 2 << 10 // 2 KiB

// MaxSizeExpensive is the upper limit for using expensive obfuscators (split, seed).
// Above this size, only cheap obfuscators are used.
const MaxSizeExpensive = 256

const (
	// minStringJunkBytes defines the minimum number of junk bytes to prepend or append during string obfuscation.
	minStringJunkBytes = 2
	// maxStringJunkBytes defines the maximum number of junk bytes to prepend or append during string obfuscation.
	maxStringJunkBytes = 8
)

// NameProviderFunc defines a function type that generates a string based on a random source and a base name.
type NameProviderFunc func(rand *mathrand.Rand, baseName string) string

// Options selects optional literal transformations. The zero value preserves
// Garble's default literal obfuscation.
type Options struct {
	SharedStrings bool
}

// EmbeddedValue bypasses the minimum size threshold for resolved //go:embed data.
type EmbeddedValue struct {
	Data   []byte
	String bool
}

// Obfuscate replaces literals using the default transformations.
func Obfuscate(rand *mathrand.Rand, file *ast.File, info *types.Info, linkStrings map[*types.Var]string, embeds map[ast.Expr]EmbeddedValue, nameFunc NameProviderFunc) *ast.File {
	return ObfuscateWithOptions(rand, file, info, linkStrings, embeds, nameFunc, Options{})
}

// ObfuscateWithOptions replaces literals using the selected transformations.
func ObfuscateWithOptions(rand *mathrand.Rand, file *ast.File, info *types.Info, linkStrings map[*types.Var]string, embeds map[ast.Expr]EmbeddedValue, nameFunc NameProviderFunc, options Options) *ast.File {
	or := newObfRand(rand, file, nameFunc)
	or.sharedStrings = options.SharedStrings
	// Package initializers, including their function literals, keep a shared
	// dispatcher. Each original function declaration gets a separate tree so
	// a live function cannot retain another function's lifted decoders.
	packageDispatcher := or.proxyDispatcher
	dispatchers := []*proxyDispatcher{packageDispatcher}
	pre := func(cursor *astutil.Cursor) bool {
		switch node := cursor.Node().(type) {
		case *ast.FuncDecl:
			// Obfuscating literals can push the stack frame over the //go:nosplit limit,
			// which is just 800 bytes. These funcs are mostly in the runtime,
			// so obfuscating strings in these is less important in any case.
			if node.Doc != nil {
				for _, comment := range node.Doc.List {
					dir, ok := ast.ParseDirective(token.NoPos, comment.Text)
					if ok && dir.Tool == "go" && dir.Name == "nosplit" {
						return false
					}
				}
			}
			// Cache decoder recipes only within an original function, including
			// its nested closures, never across package initializer scopes.
			or.stringCalls = make(map[string]*ast.CallExpr)
			owner := len(dispatchers)
			or.proxyDispatcher = newProxyDispatcher(rand, func(rand *mathrand.Rand, base string) string {
				return nameFunc(rand, fmt.Sprintf("literalOwner%d_%s", owner, base))
			})
			dispatchers = append(dispatchers, or.proxyDispatcher)
		case *ast.GenDecl:
			// constants are obfuscated by replacing all references with the obfuscated value
			if node.Tok == token.CONST {
				return false
			}
		case *ast.ValueSpec:
			hadValues := len(node.Values) > 0
			for i, name := range node.Names {
				obj := info.Defs[name].(*types.Var)
				value, ok := linkStrings[obj]
				if !ok || !types.Identical(obj.Type(), types.Typ[types.String]) {
					continue
				}
				if len(node.Values) == 0 {
					for range node.Names {
						node.Values = append(node.Values, &ast.BasicLit{Kind: token.STRING, Value: `""`})
					}
				} else if hadValues && (len(node.Values) != len(node.Names) || info.Types[node.Values[i]].Value == nil) {
					// Like cmd/link, leave non-constant initializers alone.
					continue
				}
				expr := ast.Expr(&ast.BasicLit{Kind: token.STRING, Value: strconv.Quote(value)})
				if len(value) >= MinSize && len(value) <= MaxSize {
					expr = obfuscateString(or, value)
				}
				node.Values[i] = withPos(expr, name.Pos()).(ast.Expr)
			}

		case ast.Expr:
			if value, ok := embeds[node]; ok {
				var replacement ast.Node
				if value.String {
					replacement = obfuscateString(or, string(value.Data))
				} else {
					replacement = obfuscateByteSlice(or, false, value.Data)
				}
				cursor.Replace(withPos(replacement, node.Pos()))
				return false
			}
			// A constant string converted to a byte or rune slice has an
			// exact capacity. Decoding first can make the allocation larger.
			if call, ok := node.(*ast.CallExpr); ok && len(call.Args) == 1 {
				if slice, ok := info.TypeOf(call.Fun).Underlying().(*types.Slice); ok && (slice.Elem() == types.Universe.Lookup("byte").Type() || slice.Elem() == types.Universe.Lookup("rune").Type()) {
					elem := slice.Elem()
					if value := info.Types[call.Args[0]].Value; value != nil && value.Kind() == constant.String {
						text := constant.StringVal(value)
						if len(text) >= MinSize {
							size := len(text)
							if elem == types.Universe.Lookup("rune").Type() {
								size = utf8.RuneCountInString(text)
							}
							name := or.nameFunc(or.rnd, "literalSlice")
							result := ast.NewIdent(name)
							converted := ah.CallExpr(call.Fun, obfuscateString(or, text))
							body := ah.BlockStmt(
								ah.AssignDefineStmt(result, converted),
								ah.ReturnStmt(&ast.SliceExpr{
									X:    ast.NewIdent(name),
									High: ah.IntLit(size),
									Max:  ah.IntLit(size),
								}),
							)
							cursor.Replace(withPos(ah.LambdaCall(nil, call.Fun, body, nil), node.Pos()))
							return false
						}
					}
				}
			}
			// Rewrite &[]byte{...} as a whole on the way down. Rewriting the
			// composite literal on its own would leave behind &(decoder()),
			// which is not addressable, and parentheses in the input would
			// hide the literal from a check on the way up.
			//
			// See issue #520.
			if unary, ok := node.(*ast.UnaryExpr); ok && unary.Op == token.AND {
				if lit, ok := ast.Unparen(unary.X).(*ast.CompositeLit); ok {
					if newNode := handleCompositeLiteral(or, true, lit, info); newNode != nil {
						cursor.Replace(newNode)
						return false
					}
				}
			}

			// The compiler folds constant expressions, so only the outermost
			// one exists at run time. Rewrite that one and stop descending,
			// rather than also rewriting its operands into dead decoders.
			typeAndValue := info.Types[node]
			if typeAndValue.Value == nil {
				break
			}
			if typeAndValue.Value.Kind() != constant.String {
				// Constants of other kinds, such as len or unsafe.Sizeof, do
				// not evaluate their operands at all. Rewriting them would be
				// useless, and would stop uses which require a constant, such
				// as array lengths or keyed indexes, from compiling.
				return false
			}
			if typeAndValue.Type == types.Typ[types.String] {
				value := constant.StringVal(typeAndValue.Value)
				if len(value) >= MinSize {
					cursor.Replace(withPos(obfuscateString(or, value), node.Pos()))
					return false
				}
			}
			// Keep descending: a string constant we left alone, such as one
			// below MinSize or one of a named type, may still have operands
			// which we can rewrite.
		}
		return true
	}

	post := func(cursor *astutil.Cursor) bool {
		if _, ok := cursor.Node().(*ast.FuncDecl); ok {
			or.proxyDispatcher = packageDispatcher
			or.stringCalls = nil
		}
		// Here we handle the plain []byte{...} or [4]byte{...} value form.
		// The pointer form was already replaced on the way down; a literal
		// which we declined there is declined here just the same.
		if lit, ok := cursor.Node().(*ast.CompositeLit); ok {
			if newNode := handleCompositeLiteral(or, false, lit, info); newNode != nil {
				cursor.Replace(newNode)
			}
		}
		return true
	}

	newFile := astutil.Apply(file, pre, post).(*ast.File)
	newFile.Decls = append(newFile.Decls, or.liftedFuncs...)
	for _, dispatcher := range dispatchers {
		dispatcher.AddToFile(newFile)
	}
	return newFile
}

// generatedNames assigns each decoder-local name before building its AST.
// References receive fresh Ident nodes with the same generated spelling.
type generatedNames struct {
	r     *obfRand
	names map[string]string
}

func newGeneratedNames(r *obfRand) *generatedNames {
	return &generatedNames{r: r, names: make(map[string]string)}
}

func (n *generatedNames) name(original string) string {
	if name, ok := n.names[original]; ok {
		return name
	}
	name := n.r.nameFunc(n.r.rnd, "literalLocal"+original)
	n.names[original] = name
	return name
}

func (n *generatedNames) ident(original string) *ast.Ident {
	return ast.NewIdent(n.name(original))
}

// liftCall moves a literal decoder out of its owner function and makes it a
// top-level function. The function value remains hidden in the proxy tree, so
// calls stay indirect and the compiler cannot inline the decoder back into its
// owner. Literal-heavy owners therefore no longer accumulate thousands of
// decoder closures or their inlined bodies.
func (r *obfRand) liftCall(params *ast.FieldList, resultType ast.Expr, block *ast.BlockStmt, args []ast.Expr) *ast.CallExpr {
	name := r.nextLiftedFuncName("literalDecoder")
	results := &ast.FieldList{List: []*ast.Field{{Type: resultType}}}
	r.liftedFuncs = append(r.liftedFuncs, &ast.FuncDecl{
		Name: ast.NewIdent(name),
		Type: &ast.FuncType{
			Params:  params,
			Results: results,
		},
		Body: block,
	})
	hiddenType := &ast.FuncType{
		Params:  unnamedFieldList(params),
		Results: unnamedFieldList(results),
	}
	callee := r.proxyDispatcher.HideValue(ast.NewIdent(name), hiddenType)
	return ah.CallExpr(callee, args...)
}

// liftFuncValue turns a generated function literal into an independently
// compiled top-level function while still returning it through the proxy
// dispatcher. In particular, this keeps thousands of []byte-to-string helper
// bodies out of the proxy root's global initializer; the initializer retains
// only their function values.
func (r *obfRand) liftFuncValue(funcVal *ast.FuncLit) ast.Expr {
	name := r.nextLiftedFuncName("literalHelper")
	r.liftedFuncs = append(r.liftedFuncs, &ast.FuncDecl{
		Name: ast.NewIdent(name),
		Type: funcVal.Type,
		Body: funcVal.Body,
	})
	return ast.NewIdent(name)
}

func unnamedFieldList(fields *ast.FieldList) *ast.FieldList {
	if fields == nil {
		return nil
	}
	result := &ast.FieldList{}
	for _, field := range fields.List {
		count := max(1, len(field.Names))
		for range count {
			result.List = append(result.List, &ast.Field{Type: cloneGeneratedType(field.Type)})
		}
	}
	return result
}

// cloneGeneratedType copies the small set of type expressions emitted by the
// literal obfuscator. Keeping the proxy field's function type independent from
// the lifted declaration avoids sharing AST nodes between two syntax parents.
func cloneGeneratedType(expr ast.Expr) ast.Expr {
	switch expr := expr.(type) {
	case *ast.Ident:
		return ast.NewIdent(expr.Name)
	case *ast.BasicLit:
		return &ast.BasicLit{Kind: expr.Kind, Value: expr.Value}
	case *ast.ArrayType:
		var length ast.Expr
		if expr.Len != nil {
			length = cloneGeneratedType(expr.Len)
		}
		return &ast.ArrayType{Len: length, Elt: cloneGeneratedType(expr.Elt)}
	case *ast.StarExpr:
		return &ast.StarExpr{X: cloneGeneratedType(expr.X)}
	case *ast.FuncType:
		return &ast.FuncType{
			Params:  unnamedFieldList(expr.Params),
			Results: unnamedFieldList(expr.Results),
		}
	default:
		panic(fmt.Sprintf("unsupported generated literal type %T", expr))
	}
}

func (r *obfRand) nextLiftedFuncName(base string) string {
	name := r.nameFunc(r.rnd, fmt.Sprintf("%s%d", base, r.liftedFuncSeq))
	r.liftedFuncSeq++
	return name
}

// handleCompositeLiteral checks if the input node is []byte or [...]byte and
// calls the appropriate obfuscation method, returning a new node that should
// be used to replace it.
//
// If the input node cannot be obfuscated nil is returned.
func handleCompositeLiteral(or *obfRand, isPointer bool, node *ast.CompositeLit, info *types.Info) ast.Node {
	if len(node.Elts) < MinSize {
		return nil
	}

	byteType := types.Universe.Lookup("byte").Type()

	var arrayLen int64
	switch y := info.TypeOf(node.Type).(type) {
	case *types.Array:
		if y.Elem() != byteType {
			return nil
		}

		arrayLen = y.Len()

	case *types.Slice:
		if y.Elem() != byteType {
			return nil
		}

	default:
		return nil
	}

	data := make([]byte, 0, len(node.Elts))

	for _, el := range node.Elts {
		elType := info.Types[el]

		if elType.Value == nil || elType.Value.Kind() != constant.Int {
			return nil
		}

		value, ok := constant.Uint64Val(elType.Value)
		if !ok {
			panic(fmt.Sprintf("cannot parse byte value: %v", elType.Value))
		}

		data = append(data, byte(value))
	}

	if arrayLen > 0 {
		return withPos(obfuscateByteArray(or, isPointer, data, arrayLen), node.Pos())
	}

	return withPos(obfuscateByteSlice(or, isPointer, data), node.Pos())
}

// withPos sets any token.Pos fields under node which affect printing to pos.
// Note that we can't set all token.Pos fields, since some affect the semantics.
//
// This function is useful so that go/printer doesn't try to estimate position
// offsets, which can end up in printing comment directives too early.
//
// We don't set any "end" or middle positions, because they seem irrelevant.
func withPos(node ast.Node, pos token.Pos) ast.Node {
	for node := range ast.Preorder(node) {
		switch node := node.(type) {
		case *ast.BasicLit:
			node.ValuePos = pos
		case *ast.Ident:
			node.NamePos = pos
		case *ast.CompositeLit:
			node.Lbrace = pos
			node.Rbrace = pos
		case *ast.ArrayType:
			node.Lbrack = pos
		case *ast.FuncType:
			node.Func = pos
		case *ast.BinaryExpr:
			node.OpPos = pos
		case *ast.StarExpr:
			node.Star = pos
		case *ast.CallExpr:
			node.Lparen = pos
			node.Rparen = pos

		case *ast.GenDecl:
			node.TokPos = pos
		case *ast.ReturnStmt:
			node.Return = pos
		case *ast.ForStmt:
			node.For = pos
		case *ast.RangeStmt:
			node.For = pos
		case *ast.BranchStmt:
			node.TokPos = pos
		}
	}
	return node
}

func obfuscateString(or *obfRand, data string) *ast.CallExpr {
	if call := or.stringCalls[data]; call != nil {
		return or.proxyDispatcher.cloneStringCall(call).(*ast.CallExpr)
	}
	if or.sharedStrings && len(data) >= 32 {
		call := or.sharedBlobStringCall(data)
		if or.stringCalls != nil {
			or.stringCalls[data] = call
			return or.proxyDispatcher.cloneStringCall(call).(*ast.CallExpr)
		}
		return call
	}
	obf := or.pickObfuscator(len(data))

	// Generate junk bytes to to prepend and append to the data.
	// This is to prevent the obfuscated string from being easily fingerprintable.
	junkBytes := make([]byte, or.rnd.Intn(maxStringJunkBytes-minStringJunkBytes)+minStringJunkBytes)
	or.rnd.Read(junkBytes)
	splitIdx := or.rnd.Intn(len(junkBytes))

	names := newGeneratedNames(or)
	extKeys := randExtKeys(or.rnd, names)

	plainData := []byte(data)
	plainDataWithJunkBytes := append(append(junkBytes[:splitIdx], plainData...), junkBytes[splitIdx:]...)

	block := obf.obfuscate(or.rnd, names, plainDataWithJunkBytes, extKeys)
	params, args := extKeysToParams(or, extKeys)

	hiddenCastFunc, funcTyp := or.stringConversionAdapter()
	castParamName := names.name("garbleStringCaster")
	params.List = append(params.List, &ast.Field{
		Names: []*ast.Ident{ast.NewIdent(castParamName)},
		Type:  cloneGeneratedType(funcTyp),
	})
	args = append(args, hiddenCastFunc)
	block.List = append(block.List, ah.ReturnStmt(ah.CallExpr(ast.NewIdent(castParamName), names.ident("data"), ah.IntLit(splitIdx), ah.IntLit(splitIdx+len(plainData)))))
	call := or.liftCall(params, ast.NewIdent("string"), block, args)
	if or.stringCalls != nil {
		or.stringCalls[data] = call
		return or.proxyDispatcher.cloneStringCall(call).(*ast.CallExpr)
	}
	return call
}

func (or *obfRand) sharedBlobStringCall(data string) *ast.CallExpr {
	if or.blobStringDecoder == "" {
		or.blobStringDecoder = or.nextLiftedFuncName("sharedBlobStringDecoder")
		body := sharedBlobDecodeBody()
		source := fmt.Sprintf("package p\nfunc %s(input string, low, high int) string { decode := func(input string) []byte %s; return string(decode(input)[low:high]) }", or.blobStringDecoder, body)
		parsed, err := parser.ParseFile(token.NewFileSet(), "", source, 0)
		if err != nil {
			panic(err)
		}
		clearNodePositions(parsed.Decls[0])
		or.liftedFuncs = append(or.liftedFuncs, parsed.Decls...)
	}
	junkBytes := make([]byte, or.rnd.Intn(maxStringJunkBytes-minStringJunkBytes)+minStringJunkBytes)
	or.rnd.Read(junkBytes)
	splitIdx := or.rnd.Intn(len(junkBytes))
	plain := []byte(data)
	plainWithJunk := append(append(junkBytes[:splitIdx], plain...), junkBytes[splitIdx:]...)
	encoded := encodeSharedBlob(or.rnd, plainWithJunk)
	return ah.CallExpr(ast.NewIdent(or.blobStringDecoder), ah.StringLit(string(encoded)), ah.IntLit(splitIdx), ah.IntLit(splitIdx+len(plain)))
}

// Parsed decoder positions belong to a temporary file set. Leave the lifted
// function positionless so non-tiny source mapping treats it as generated code.
func clearNodePositions(node ast.Node) {
	positionType := reflect.TypeFor[token.Pos]()
	for n := range ast.Preorder(node) {
		value := reflect.ValueOf(n).Elem()
		for i := range value.NumField() {
			field := value.Field(i)
			if field.CanSet() && field.Type() == positionType {
				field.SetInt(0)
			}
		}
	}
}

// The selected literal calls always contain a mode and a key followed by ciphertext.
// Unlike embed.FS blobs, these values need no magic header: a fixed marker
// would make extraction from a binary unnecessarily simple.
func sharedBlobDecodeBody() string {
	keySize := BlobHeaderSize - len(BlobMagic)
	return fmt.Sprintf(`{
mode := input[0]
key := input[1:%d]
decoded := []byte(input[%d:])
for i, b := range decoded {
 k := key[i %% len(key)]
 switch mode {
 case 0: decoded[i] = b ^ k
 case 1: decoded[i] = b - k
 case 2: decoded[i] = b + k
 default: x := b ^ k; decoded[i] = x >> 3 | x << 5
 }
}
return decoded[:len(decoded):len(decoded)]
}`, keySize+1, keySize+1)
}

func encodeSharedBlob(rand *mathrand.Rand, plain []byte) []byte {
	encoded := EncodeBlob(rand, plain)[len(BlobMagic):]
	keySize := BlobHeaderSize - len(BlobMagic)
	key, ciphertext := encoded[:keySize], encoded[keySize:]
	mode := byte(rand.Intn(4))
	for i, b := range plain {
		k := key[i%len(key)]
		switch mode {
		case 0:
			ciphertext[i] = b ^ k
		case 1:
			ciphertext[i] = b + k
		case 2:
			ciphertext[i] = b - k
		case 3:
			ciphertext[i] = (b<<3 | b>>5) ^ k
		}
	}
	return append([]byte{mode}, encoded...)
}

// Each use needs independent positions; only the hidden values and decoder are
// shared, not mutable AST nodes or the result of running the decoder.
func (d *proxyDispatcher) cloneStringCall(expr ast.Expr) ast.Expr {
	switch expr := expr.(type) {
	case *ast.CallExpr:
		args := make([]ast.Expr, len(expr.Args))
		for i, arg := range expr.Args {
			args[i] = d.cloneStringCall(arg)
		}
		return &ast.CallExpr{Fun: d.cloneStringCall(expr.Fun), Args: args}
	case *ast.SelectorExpr:
		return d.clonePath(expr)
	case *ast.Ident:
		return ast.NewIdent(expr.Name)
	case *ast.BasicLit:
		return &ast.BasicLit{Kind: expr.Kind, Value: expr.Value}
	default:
		panic(fmt.Sprintf("unsupported string decoder expression %T", expr))
	}
}

// stringConversionAdapter shares only within the current owner's dispatcher.
// Bounds stay in each decoder, so junk and different literal lengths do not
// require separate conversion functions.
func (r *obfRand) stringConversionAdapter() (ast.Expr, *ast.FuncType) {
	d := r.proxyDispatcher
	if d.stringAdapter == nil {
		names := newGeneratedNames(r)
		funcVal := &ast.FuncLit{
			Type: &ast.FuncType{
				Params: &ast.FieldList{List: []*ast.Field{
					ah.Field(ah.ByteSliceType(), names.ident("x")),
					ah.Field(ast.NewIdent("int"), names.ident("low")),
					ah.Field(ast.NewIdent("int"), names.ident("high")),
				}},
				Results: &ast.FieldList{List: []*ast.Field{{Type: ast.NewIdent("string")}}},
			},
			Body: ah.BlockStmt(ah.ReturnStmt(ah.CallExprByName("string", &ast.SliceExpr{
				X: names.ident("x"), Low: names.ident("low"), High: names.ident("high"),
			}))),
		}
		d.stringAdapterType = cloneGeneratedType(funcVal.Type).(*ast.FuncType)
		d.stringAdapter = d.HideValue(r.liftFuncValue(funcVal), d.stringAdapterType)
	}
	return d.clonePath(d.stringAdapter), d.stringAdapterType
}

func obfuscateByteSlice(or *obfRand, isPointer bool, data []byte) *ast.CallExpr {
	obf := or.pickObfuscator(len(data))

	names := newGeneratedNames(or)
	extKeys := randExtKeys(or.rnd, names)
	block := obf.obfuscate(or.rnd, names, data, extKeys)
	params, args := extKeysToParams(or, extKeys)

	if isPointer {
		block.List = append(block.List, ah.ReturnStmt(
			ah.UnaryExpr(token.AND, names.ident("data")),
		))
		return or.liftCall(params, ah.StarExpr(ah.ByteSliceType()), block, args)
	}

	block.List = append(block.List, ah.ReturnStmt(names.ident("data")))
	return or.liftCall(params, ah.ByteSliceType(), block, args)
}

func obfuscateByteArray(or *obfRand, isPointer bool, data []byte, length int64) *ast.CallExpr {
	obf := or.pickObfuscator(len(data))

	names := newGeneratedNames(or)
	extKeys := randExtKeys(or.rnd, names)
	block := obf.obfuscate(or.rnd, names, data, extKeys)
	params, args := extKeysToParams(or, extKeys)

	arrayType := ah.ByteArrayType(length)

	sliceToArray := []ast.Stmt{
		&ast.DeclStmt{
			Decl: &ast.GenDecl{
				Tok: token.VAR,
				Specs: []ast.Spec{&ast.ValueSpec{
					Names: []*ast.Ident{names.ident("newdata")},
					Type:  arrayType,
				}},
			},
		},
		&ast.RangeStmt{
			Key: names.ident("i"),
			Tok: token.DEFINE,
			X:   names.ident("data"),
			Body: ah.BlockStmt(
				ah.AssignStmt(
					ah.IndexExprByExpr(names.ident("newdata"), names.ident("i")),
					ah.IndexExprByExpr(names.ident("data"), names.ident("i")),
				),
			),
		},
	}

	var retexpr ast.Expr = names.ident("newdata")
	if isPointer {
		retexpr = ah.UnaryExpr(token.AND, retexpr)
	}

	sliceToArray = append(sliceToArray, ah.ReturnStmt(retexpr))
	block.List = append(block.List, sliceToArray...)

	if isPointer {
		return or.liftCall(params, ah.StarExpr(arrayType), block, args)
	}

	return or.liftCall(params, arrayType, block, args)
}

func (or *obfRand) pickObfuscator(size int) obfuscator {
	if size < MinSize || size > MaxSize {
		return blob{}
	}
	if or.testObfuscator != nil {
		return or.testObfuscator
	}
	if size <= MaxSizeExpensive {
		return Obfuscators[or.rnd.Intn(len(Obfuscators))]
	}
	return CheapObfuscators[or.rnd.Intn(len(CheapObfuscators))]
}
