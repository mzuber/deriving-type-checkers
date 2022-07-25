class Pair extends Object {
    Object fst;
    Object snd;

    Pair(Object fst, Object snd) {
        super();
        this.fst=fst;
    }

    Pair setfst(Object newfst) {
        return new Pair(newfst, this.snd);
    }
}
