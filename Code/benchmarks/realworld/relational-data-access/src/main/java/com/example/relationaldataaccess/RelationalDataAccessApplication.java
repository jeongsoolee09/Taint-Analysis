package com.example.relationaldataaccess;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.CommandLineRunner;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.jdbc.core.JdbcTemplate;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.Scanner;
import java.util.Map;

@SpringBootApplication
public class RelationalDataAccessApplication implements CommandLineRunner {

    @Autowired
    JdbcTemplate jdbcTemplate;
    private static final Logger log = LoggerFactory.getLogger(RelationalDataAccessApplication.class);

    public static void main(String[] args) {
        SpringApplication.run(RelationalDataAccessApplication.class, args);
    }

    public String[] create() {
        Scanner scanner = new Scanner(System.in);
        String firstName = scanner.nextLine();
        String lastName = scanner.nextLine();
        String[] out = new String[2];
        out[0] = firstName;
        out[1] = lastName;

        return out;
    }

    @Override
    public void run(String... strings) throws Exception {
        String[] splitUpNames = create();
        String firstName = splitUpNames[0];
        String lastName = splitUpNames[1];
        jdbcTemplate.batchUpdate("INSERT INTO customers(first_name, last_name) VALUES ("+firstName+","+lastName+")");
    }

    public Map<String, Object> query() throws Exception {
        Map<String, Object> results = jdbcTemplate.queryForMap("SELECT id, first_name, last_name FROM customers WHERE first_name = ?", new Object[] { });
        return results;
    }

    public void printer(Map<String, Object> results) throws Exception {
        for (Object name : results.values())
            System.out.println("name: " + name);
    }
}
