class MethInvk extends Object {
    Foo attribute;

    MethInvk (Foo attribute) {
        super();
        this.attribute = attribute;
    }

    Object invoke(Foo param) {
        return param.getBar();
    }
}

class Foo extends Object {
	Object bar;
	
	Foo (Object bar) {
		super();
		this.bar = bar;
	}
	
	Object getBar() {
		return this.bar;
	}
}