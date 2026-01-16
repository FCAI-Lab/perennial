package strings

func StringToByteSlice(s string) (a []byte) {
	for i := range len(s) {
		a = append(a, s[i])
	}
	return
}

func ByteSliceToString(a []byte) (s string) {
	for _, c := range a {
		s = s + string(c)
	}
	return
}
