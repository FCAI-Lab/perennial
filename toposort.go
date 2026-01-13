package goose

// uses depth first search
func toposortVisit[V comparable](vs []V, deps func(v V)[]V, f func(v V),
	handleCycle func(vs []V)) {
	visited := make(map[V]bool)
	dipath := make([]V, 0)
	onDipath := make(map[V]bool)

	var visit func(v V)
	visit = func(v V) {
		if visited[v] {
			return
		} else if onDipath[v] {
			handleCycle(dipath)
		} else {
			dipath, onDipath[v] = append(dipath, v), true
			for _, d := range deps(v) {
				visit(d)
			}
		}
		visited[v] = true
		delete(onDipath, v)
		dipath = dipath[:len(dipath)-1]
		f(v)
	}

	for _, v := range vs {
		visit(v)
	}

	return
}
