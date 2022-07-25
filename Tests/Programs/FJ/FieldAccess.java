class FieldAccess extends Object {
    Object attribute;

    FieldAccess (Object attribute) {
        super();
        this.attribute = attribute;
    }

    Object getAttribute() {
        return this.attribute;
    }
}
