import java.lang.Integer;

public abstract class PageableFactory {

	public static Integer first(int count) {
		return build(0, count);
	}

    public static Integer forLists(int page) {
        return build(page - 1, 10);
    }

    public static Integer forDashboard(int page) {
        return build(page - 1, 30);
    }

    public static Integer forFeeds() {
        return build(0, 20);
    }

    private static Integer build(int page, int pageSize) {
        return new Integer(page+pageSize);
    }
}
