# 채점에 필요한 정답지

correct_solution_WhatIWantExample = dict([
    ('void PrintStream.println(int)', 'sin'),
    ('void WhatIWantExample.g(int)', 'san'),
    ('void WhatIWantExample.m3(int)', 'sin'),
    ('void WhatIWantExample.h(int)', 'non'),
    ('void WhatIWantExample.main()', 'non'),
    ('int WhatIWantExample.m2(int)', 'san'),
    ('void WhatIWantExample.f()', 'src'),
    ('int WhatIWantExample.m1()', 'src')
])

correct_solution_relational = dict([
    ("void JdbcTemplate.execute(String)", "sin"),
    ("void RelationalDataAccessApplication.run(java.lang.String[])", "sin"),
    ("ConfigurableApplicationContext SpringApplication.run(Class,java.lang.String[])", "non"),
    ("int[] JdbcTemplate.batchUpdate(String,List)", "sin"),
    ("void RelationalDataAccessApplication.createTable()", "sin"),
    ("String Customer.toString()", "non"),
    ("Object Stream.collect(Collector)", "non"),
    ("void List.forEach(Consumer)", "non"),
    ("void Logger.info(String)", "sin"),
    ("Collector Collectors.toList()", "non"),
    ("String String.format(String,java.lang.Object[])", "non"),
    ("void RelationalDataAccessApplication.query()", "sin"),
    ("List Arrays.asList(java.lang.Object[])", "non"),
    ("Long Long.valueOf(long)", "non"),
    ("void RelationalDataAccessApplication.main(java.lang.String[])", "non"),
    ("List Creator.create()", "src"),
    ("Stream List.stream()", "non"),
    ("Stream Stream.map(Function)", "non"),
    ("List JdbcTemplate.query(String,java.lang.Object[],RowMapper)", "sin")
])
