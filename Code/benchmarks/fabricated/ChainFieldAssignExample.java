class Struct {
	int f;

	Struct() {
	}
}


class ChainFieldAssignExample {
    public static void main() {
	Struct x = new Struct();
	Struct y = new Struct();
	Struct z = new Struct();
	Struct u = new Struct();

	x.f = 1;
	y.f = x.f;
	z.f = y.f;
	u.f = z.f;
    }
}

