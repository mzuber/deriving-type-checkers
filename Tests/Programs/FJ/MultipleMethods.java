class Foo extends Object {
	Object a;
    Object b;

    Foo (Object a, Object b) {
        super();
        this.a = a;
		this.b = b;
    }

    Object getA() {
        return this.a;
    }
	
	Object getB() {
		return this.b;
	}
}
