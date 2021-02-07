/**
 * Copyright (C) 2014 Stratio (http://stratio.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *         http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.stratio.decision.shell.configuration;

import org.springframework.beans.factory.annotation.Value;
import org.springframework.cache.annotation.EnableCaching;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.PropertySource;

import com.stratio.decision.api.IStratioStreamingAPI;
import com.stratio.decision.api.StratioStreamingAPIFactory;


@Configuration
@PropertySource("classpath:shell.properties")
@EnableCaching
public class StreamingApiConfiguration {


    @Value("${kafka.brokers}")
    private String kafkaBrokers;

    @Value("${zookeeper.quorum}")
    private String zkQuorum;

    @Value("${kafka.zookeeperPath}")
    private String zkPath;

    @Bean
    public IStratioStreamingAPI stratioStreamingApi() {
        return StratioStreamingAPIFactory.create().
                withQuorumConfig(kafkaBrokers, zkQuorum, zkPath);
    }

}
