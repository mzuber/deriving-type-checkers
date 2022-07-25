class Cast extends Object {
	Object a;
    Object b;

    Cast (Object a, Object b) {
        super();
        this.a = a;
		this.b = b;
    }

    A getB() {
        return (B) this.b;
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

class B extends Object {
    Object b;
	
    B (Object b) {
        super();
        this.b = b;
    }
	
    Object getB() {
        return this.b;
    }
}
