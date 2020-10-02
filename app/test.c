int main(int b) {
	int a = 1;
	if (b == 1) {
		do {
			a += b;
		} while (a == 1);
	} else {
		a -= b;
	}
	return 1;
}

int f() {
	int c = 0;
	for (int i = 0; i < 10; i++) {
		c--;
	}
	return 0;
}
