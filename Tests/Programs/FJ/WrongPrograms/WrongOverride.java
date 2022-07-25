class A extends Object {
    Object a;

    A (Object a) {
        super();
        this.a = a;
    }

    A setA(Object newA) {
        return new A(newA);
    }
}

class B extends A {
    Object b;

    B (Object a, Object b) {
        super(a);
        this.b = b;
    }

    A setA(A newA) {
        return new C(newA);
    }
}

class C extends Object {
    A a;
	
    C (A a) {
        super();
        this.a = a;
    }
}