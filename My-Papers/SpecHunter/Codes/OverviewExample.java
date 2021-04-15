@SpringBootApplication
public class RelationalData {

    @Autowired
    JdbcTemplate jdbcTemplate;
    Logger log = LoggerFactory.getLogger(RelationalDataAccessApplication.class);

    public static void main(String[] args) {
        SpringApplication.run(RelationalDataAccessApplication.class, args);
    }

    public String create() {
        Scanner scanner = new Scanner(System.in);
        String name = scanner.nextLine();
        return name;
    }

    public void run() throws Exception {
        String name = create();
        String sql = "INSERT INTO customers VALUES (" + name + ")";
        jdbcTemplate.batchUpdate(sql);
    }

    public Map<String, Object> query() throws Exception {
        Map<String, Object> results = jdbcTemplate.queryForMap("SELECT id, first_name, FROM customers WHERE first_name = ?", new Object[] { "John" });
        return results;
    }

    public void printer(Map<String, Object> results) throws Exception {
       Object elem = results.get("John");
       log.info(elem);
    }

    public void bridge() throws Exception {
        Map<String, Object> queryResult = query();
        printer(queryResult);
    }
}
