package channel_examples

// prog3 from Actris 2.0 intro: https://arxiv.org/pdf/2010.15030
func DSPExample() int {
	c := make(chan any)
	signal := make(chan any)

	go func() {
		ptr := (<-c).(*int)  // receive pointer ℓ
		*ptr = *ptr + 2      // update *ℓ to *ℓ + 2
		signal <- struct{}{} // send signal ()
	}()

	val := 40
	ptr := &val // create reference ℓ := ref 40
	c <- ptr    // send pointer ℓ
	<-signal    // receive signal
	return *ptr // dereference to get 42
}
