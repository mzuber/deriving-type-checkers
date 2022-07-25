class ObjectCreation extends Object {
    Object attribute;

    ObjectCreation (Object attribute) {
        super();
        this.attribute = attribute;
    }

    ObjectCreation setAttribute(Object newAttribute) {
        return new ObjectCreation();
    }
}
