// Copyright (c) 2026, The Garble Authors.
// See LICENSE for licensing information.

package literals

import (
	"fmt"
	"go/ast"
	"math/rand"
	"strconv"
	"strings"
	"testing"
)

func TestSharedStringOption(t *testing.T) {
	newRand := func() *obfRand {
		return newObfRand(rand.New(rand.NewSource(7)), &ast.File{Name: ast.NewIdent("main")},
			func(r *rand.Rand, base string) string { return fmt.Sprintf("%s%d", base, r.Uint64()) })
	}
	plain := newRand()
	plain.stringCalls = make(map[string]*ast.CallExpr)
	obfuscateString(plain, strings.Repeat("x", 32))
	if plain.blobStringDecoder != "" {
		t.Fatal("default path unexpectedly uses the shared decoder")
	}

	shared := newRand()
	shared.sharedStrings = true
	shared.stringCalls = make(map[string]*ast.CallExpr)
	obfuscateString(shared, strings.Repeat("a", 31))
	if shared.blobStringDecoder != "" {
		t.Fatal("short string unexpectedly uses the shared decoder")
	}
	first := obfuscateString(shared, strings.Repeat("a", 32))
	second := obfuscateString(shared, strings.Repeat("b", 64))
	if shared.blobStringDecoder == "" || first.Fun.(*ast.Ident).Name != shared.blobStringDecoder || second.Fun.(*ast.Ident).Name != shared.blobStringDecoder {
		t.Fatal("long strings do not share the decoder")
	}
	if again := obfuscateString(shared, strings.Repeat("a", 32)); again.Fun.(*ast.Ident).Name != shared.blobStringDecoder {
		t.Fatal("repeated string lost the shared decoder")
	}
	var previousKey string
	for _, call := range []*ast.CallExpr{first, second} {
		quoted := call.Args[0].(*ast.BasicLit).Value
		encoded, err := strconv.Unquote(quoted)
		if err != nil {
			t.Fatal(err)
		}
		if strings.Contains(encoded, BlobMagic) || len(encoded) < BlobHeaderSize-len(BlobMagic)+1 {
			t.Fatal("shared string retains a blob magic header or has no key")
		}
		keySize := BlobHeaderSize - len(BlobMagic)
		key := encoded[1 : keySize+1]
		if key == previousKey {
			t.Fatal("distinct strings reuse the same key")
		}
		previousKey = key
		ciphertext := decodeSharedTest(encoded)
		low, err := strconv.Atoi(call.Args[1].(*ast.BasicLit).Value)
		if err != nil {
			t.Fatal(err)
		}
		high, err := strconv.Atoi(call.Args[2].(*ast.BasicLit).Value)
		if err != nil {
			t.Fatal(err)
		}
		if got := string(ciphertext[low:high]); got != strings.Repeat("a", 32) && got != strings.Repeat("b", 64) {
			t.Fatalf("shared decoder recovered %q", got)
		}
	}
	before := len(shared.liftedFuncs)
	obfuscateByteSlice(shared, false, []byte(strings.Repeat("c", 32)))
	if len(shared.liftedFuncs) != before+1 {
		t.Fatal("byte slice did not keep its independent decoder")
	}
}

func TestSharedDecoderHasNoSourcePositions(t *testing.T) {
	or := newObfRand(rand.New(rand.NewSource(7)), &ast.File{Name: ast.NewIdent("main")},
		func(r *rand.Rand, base string) string { return fmt.Sprintf("%s%d", base, r.Uint64()) })
	or.sharedStrings = true
	or.sharedBlobStringCall(strings.Repeat("x", 32))

	// Non-tiny source mapping recognizes generated functions only when every
	// node is positionless. Parser positions belong to a different file set.
	decoder := or.liftedFuncs[0].(*ast.FuncDecl)
	for node := range ast.Preorder(decoder) {
		if node.Pos().IsValid() {
			t.Fatalf("generated shared decoder has source position %v in %T", node.Pos(), node)
		}
	}
}

func decodeSharedTest(encoded string) []byte {
	keySize := BlobHeaderSize - len(BlobMagic)
	mode := encoded[0]
	key, decoded := encoded[1:keySize+1], []byte(encoded[keySize+1:])
	for i, b := range decoded {
		k := key[i%len(key)]
		switch mode {
		case 0:
			decoded[i] = b ^ k
		case 1:
			decoded[i] = b - k
		case 2:
			decoded[i] = b + k
		case 3:
			x := b ^ k
			decoded[i] = x>>3 | x<<5
		default:
			panic("invalid shared literal mode")
		}
	}
	return decoded
}

func TestEncodeSharedModes(t *testing.T) {
	plain := []byte(strings.Repeat("mixed-literal-value-", 4))
	seen := make(map[byte]bool)
	for seed := int64(0); seed < 100; seed++ {
		encoded := encodeSharedBlob(rand.New(rand.NewSource(seed)), plain)
		seen[encoded[0]] = true
		if got := decodeSharedTest(string(encoded)); string(got) != string(plain) {
			t.Fatalf("seed %d recovered %q", seed, got)
		}
	}
	if len(seen) != 4 {
		t.Fatalf("covered %d modes, want 4", len(seen))
	}
}

func TestSharedShortStringsKeepIndependentEncodings(t *testing.T) {
	or := newObfRand(rand.New(rand.NewSource(91)), &ast.File{Name: ast.NewIdent("main")},
		func(r *rand.Rand, base string) string { return fmt.Sprintf("%s%d", base, r.Uint64()) })
	or.sharedStrings = true
	or.sharedShortStrings = true
	value := "repeat-short-secret"
	or.stringCalls = make(map[string]*ast.CallExpr)
	var previous, previousKey string
	for i := range 3 {
		if i == 2 {
			// The third use is in a different original function.
			or.stringCalls = make(map[string]*ast.CallExpr)
		}
		call := obfuscateString(or, value)
		if call.Fun.(*ast.Ident).Name != or.blobStringDecoder {
			t.Fatal("short string did not use shared decoder")
		}
		encoded, err := strconv.Unquote(call.Args[0].(*ast.BasicLit).Value)
		if err != nil {
			t.Fatal(err)
		}
		if encoded == previous {
			t.Fatal("repeated short string reused one encoding")
		}
		previous = encoded
		keySize := BlobHeaderSize - len(BlobMagic)
		key := encoded[1 : keySize+1]
		if key == previousKey {
			t.Fatal("repeated short string reused one key")
		}
		previousKey = key
		low, err := strconv.Atoi(call.Args[1].(*ast.BasicLit).Value)
		if err != nil {
			t.Fatal(err)
		}
		high, err := strconv.Atoi(call.Args[2].(*ast.BasicLit).Value)
		if err != nil {
			t.Fatal(err)
		}
		if got := string(decodeSharedTest(encoded)[low:high]); got != value {
			t.Fatalf("decoded %q, want %q", got, value)
		}
	}
}
