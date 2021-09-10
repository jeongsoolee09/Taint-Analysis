class StringFormatExample {
    public void showPost(String year, String month, String day,
                           String slug) {
        String s = String.format("%s/%s/%s/%s", year, month, day, slug);
    }
}
