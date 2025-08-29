package unittest

const (
	a = 1.0
)

func useFloat() float64 {
	x := a
	x = (x + a) * 1.0
	return x
}
