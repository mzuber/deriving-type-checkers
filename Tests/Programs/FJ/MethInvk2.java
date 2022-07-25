class Invoke extends Object {
	Pair p;
	
	Invoke (Pair p) {
		super();
		this.p = p;
	}
	
	Object getFst(Pair p) {
		return p.getFst();
	}
	
	Pair setSnd(Pair p, Object newsnd) {
		return p.setSnd(newsnd);
	}
}

class Pair extends Object {
    Object fst;
    Object snd;

    Pair(Object fst, Object snd) {
        super();
        this.fst=fst;
        this.snd=snd;
    }

    Pair setFst(Object newfst) {
        return new Pair(newfst, this.snd);
    }
	
	Pair setSnd(Object newsnd) {
        return new Pair(this.fst, newsnd);
    }
	
	Object getFst() {
		return this.fst;
	}
	
	Object getSnd() {
		return this.snd;
	}
}
