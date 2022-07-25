class A extends Object {
    B attribute;

    A (B attribute) {
        super();
        this.attribute = attribute;
    }
	
	B getAttribute() {
		return this.attribute;
	}
}

class B extends Object {
    A attribute;

    B (A attribute) {
        super();
        this.attribute = attribute;
    }
	
	A getAttribute() {
		return this.attribute;
	}
}
