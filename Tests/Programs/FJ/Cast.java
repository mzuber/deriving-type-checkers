class Cast extends Object {
	A a;
    B b;

    Cast (A a, B b) {
        super();
        this.a = a;
		this.b = b;
    }

    A getB() {
        return (A) this.b;
    }
	
	B getA() {
		return (B) this.a;
	}
}

class A extends Object {
    Object a;
	
    A (Object a) {
        super();
        this.a = a;
    }
	
    Object getA() {
        return this.a;
    }
}

class B extends A {
    Object b;
	
    B (Object a, Object b) {
        super(a);
        this.b = b;
    }
	
    Object getB() {
        return this.b;
    }
}
