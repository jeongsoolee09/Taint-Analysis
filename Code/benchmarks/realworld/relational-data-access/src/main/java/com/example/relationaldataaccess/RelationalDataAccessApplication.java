package com.example.relationaldataaccess;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.CommandLineRunner;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.jdbc.core.JdbcTemplate;

import java.util.Scanner;
import java.util.Map;
import java.util.ArrayList;
import java.util.List;

@SpringBootApplication
public class RelationalDataAccessApplication {

    @Autowired
    JdbcTemplate jdbcTemplate;

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
        List<Object[]> args = new ArrayList();
        jdbcTemplate.batchUpdate(sql, args);
    }

    public Map<String, Object> query() throws Exception {
        Map<String, Object> results = jdbcTemplate.queryForMap("SELECT id, first_name, FROM customers WHERE first_name = ?", new Object[] { "John" });
        return results;
    }

    public void printer(Map<String, Object> results) throws Exception {
        for (Object name : results.values())
            System.out.println("name: " + name);
    }

    public void bridge() throws Exception {
        Map<String, Object> queryResult = query();
        printer(queryResult);
    }
}
