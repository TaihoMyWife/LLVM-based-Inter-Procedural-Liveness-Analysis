void test() {
	int a, b, c, e;
	e = b + c;
	if (e > 0) {
		test();
	} 
	else {
		a = b + c;
	}
	a = e + c;
}
