package channel_examples

import (
	"strings"
	"testing"
	"time"
)

// Various tests that should panic when failing, which also means verifying { True } e { True } is
// sufficient since panic can't be verified.
func TestHelloWorldSync() {
	result := HelloWorldSync()
	if result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestHelloWorldWithTimeout() {
	result := HelloWorldWithTimeout()
	if result != "operation timed out" && result != "Hello, World!" {
		panic("incorrect output")
	}
}

func TestDSPExample() {
	result := DSPExample()
	if result != 42 {
		panic("incorrect output")
	}
}

func TestFibConsumer() {
	result := fib_consumer()
	expected := []int{0, 1, 1, 2, 3, 5, 8, 13, 21, 34}

	if len(result) != len(expected) {
		panic("incorrect output")
	}

	for i := range expected {
		if result[i] != expected[i] {
			panic("incorrect output")
		}
	}
}

func TestSelectNbNotReady() {
	iterations := 10000
	for i := 0; i < iterations; i++ {
		select_nb_not_ready()
		// Small sleep to let the goroutine finish
		time.Sleep(1 * time.Microsecond)
	}
}

func TestSelectReadyCaseNoPanic() {
	iterations := 10000
	for i := 0; i < iterations; i++ {
		select_ready_case_no_panic()
	}
}

func TestAll(t *testing.T) {
	TestHelloWorldSync()
	TestHelloWorldWithTimeout()
	TestDSPExample()
	TestFibConsumer()
	TestSelectNbNotReady()
	TestSelectReadyCaseNoPanic()
}

func TestHigherOrderExample(t *testing.T) {
	responses := HigherOrderExample()
	expected := []string{"hello world", "HELLO", "world"}
	if !strings.EqualFold(strings.Join(responses, ""), strings.Join(expected, "")) {
		t.Errorf("Expected %v, got %v", expected, responses)
	}
}
