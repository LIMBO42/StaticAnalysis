class Corner{
    void nonIntParameter(int x, String s) {
        x = Integer.parseInt(s);
    }

    void nulllLValue(){
        String s = "abc";
        s.length();
    }

    void rValueInvoke(){
        int a = 0;
        String s = "abc";
        a = s.length();
        a = a+1;
    }

    String lValueObject(){
        String s;
        s = "abc";
        return s;
    }

}