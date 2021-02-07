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
package com.stratio.decision.configuration;

import com.stratio.decision.commons.constants.STREAMING;
import com.stratio.decision.utils.ZKUtils;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Configuration;

import javax.annotation.PostConstruct;

@Configuration
public class ZookeeperConfiguration {

    @Autowired
    private ConfigurationContext configurationContext;

    @PostConstruct
    public void startUp() throws Exception {
//        ZKUtils.getZKUtils(configurationContext.getZookeeperHostsQuorum()).createEphemeralZNode(
//                STREAMING.ZK_EPHEMERAL_NODE_PATH, String.valueOf(System.currentTimeMillis()).getBytes());

        String zkPath = STREAMING.ZK_BASE_PATH.concat("/").concat(configurationContext.getGroupId()).concat(STREAMING
                .ZK_EPHEMERAL_NODE);

        ZKUtils zkUtils= ZKUtils.getZKUtils(configurationContext.getZookeeperHostsQuorum(), configurationContext
                .getGroupId());
        zkUtils.createEphemeralZNode(
                zkPath, String.valueOf(System.currentTimeMillis()).getBytes());


        if (!configurationContext.getKafkaZookeeperPath().isEmpty())    {
            if (!zkUtils.existZNode(configurationContext.getKafkaZookeeperPath()))
                zkUtils.createPath(configurationContext.getKafkaZookeeperPath());
        }
    }

}
