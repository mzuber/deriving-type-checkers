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

class C extends B {
    Object c;
	
    C (Object a, Object b, Object c) {
        super(a,b);
        this.c = c;
    }
	
	Object getC() {
		return this.c;
	}
}

class D extends C {
    Object d;
	
    D (Object a, Object b, Object c, Object d) {
        super(a,b,c);
        this.d = d;
    }
	
	Object getD() {
		return this.d;
	}
}
