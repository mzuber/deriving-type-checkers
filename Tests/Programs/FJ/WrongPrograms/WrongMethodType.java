class FieldAccess extends Object {
    Object attribute;

    FieldAccess (Object attribute) {
        super();
        this.attribute = attribute;
    }

    WrongType getAttribute() {
        return this.attribute;
    }
}
