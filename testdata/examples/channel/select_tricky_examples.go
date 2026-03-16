package channel_examples

// Show that it isn't possible to have 2 nonblocking ops that match.
func select_nb_not_ready() {
	ch := make(chan struct{})
	go func() {
		select {
		case <-ch:
			panic("bad")
		default:
		}
	}()

	select {
	case ch <- struct{}{}:
		panic("bad")
	default:
	}
}

func select_nb_guaranteed_ready() {
	x := make(chan int)
	close(x)
	select {
	case <-x:
	default:
		close(x)
	}
}

// Show that a nonblocking select does not take a send case
// when the buffered channel is already full.
func select_nb_full_buffer_no_panic() {
	// 1. Buffered channel of size 1
	ch := make(chan int, 1)

	// 2. Fill the buffer
	ch <- 0

	// 3. Nonblocking select:
	//    the send case would panic,
	//    so it must NOT be taken.
	select {
	case ch <- 0:
		panic("unreachable")
	default:
		// benign: correct behavior
	}
}

// Unverifiable: Panic is irreducible
func select_nb_buffer_space_panic() {
	// Create a buffered channel with capacity 1
	ch := make(chan int, 1)

	// Nonblocking select:
	// the send case is enabled and may be chosen.
	select {
	case ch <- 0:
		// This panic is reachable
		panic("bad")
	default:
	}
}

// Blocking select: vacuously verifiable due to deadlock
func select_nb_buffer_space_deadlock() {
	// Create a buffered channel with capacity 1
	ch := make(chan int, 1)

	// First send fills the buffer
	ch <- 0

	// Blocks indefinitely on send.
	select {
	case ch <- 0:
		// This code is unreachable
		panic("unreachable")
	}
}
