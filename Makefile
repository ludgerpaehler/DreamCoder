all: solver compression helmholtz protonet-tester versionDemo logoDrawString solver_data

.PHONY: solver compression helmholtz protonet-tester versionDemo logoDrawString solver_data

clean:
	dune clean
	rm -f solver
	rm -f compression
	rm -f helmholtz
	rm -f protonet-tester
	rm -f versionDemo
	rm -f logoDrawString
	rm -f data/geom/logoDrawString
	rm -f solver_context

solver:
	dune build solvers/solver.exe
	mv solvers/solver.exe solver

compression:
	dune build solvers/compression.exe
	mv solvers/compression.exe compression

helmholtz:
	dune build solvers/helmholtz.exe
	mv solvers/helmholtz.exe helmholtz

protonet-tester:
	dune build solvers/protonet_tester.exe
	mv solvers/protonet_tester.exe protonet-tester

versionDemo:
	dune build solvers/versionDemo.exe
	mv solvers/versionDemo.exe versionDemo

logoDrawString:
	dune build solvers/logoDrawString.exe
	mv solvers/logoDrawString.exe logoDrawString
	ln -sf ../../logoDrawString data/geom/logoDrawString

solver_data:
	dune build solvers/solver_data.exe
	mv solvers/solver_data.exe solver_data
