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
package com.stratio.decision.drools;

import java.util.HashMap;
import java.util.Map;

import org.kie.api.KieServices;
import org.kie.api.runtime.KieContainer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.stratio.decision.drools.configuration.DroolsConfigurationBean;
import com.stratio.decision.drools.configuration.DroolsConfigurationGroupBean;

//import org.kie.api.builder.KieScanner;

/**
 * Created by josepablofernandez on 2/12/15.
 */
public class DroolsConnectionContainer {


    private static final Logger logger = LoggerFactory.getLogger(DroolsConnectionContainer.class);

    private Map<String, DroolsInstace> groupContainers;
    private Map<String, DroolsConfigurationGroupBean> groupConfigurations;


    public DroolsConnectionContainer(DroolsConfigurationBean droolsConfigurationBean) {

        this.groupContainers = configGroupsContainers(droolsConfigurationBean);
        this.groupConfigurations = droolsConfigurationBean.getGroups();
    }

    private Map<String, String> configGroupsSessionType(DroolsConfigurationBean droolsConfigurationBean) {

        Map<String, String> groupSessionTypes = new HashMap<>();

        if (droolsConfigurationBean != null){

            for (String groupName : droolsConfigurationBean.getListGroups()){

                DroolsConfigurationGroupBean groupConfigBean = droolsConfigurationBean.getGroups().get(groupName);
                groupSessionTypes.put(groupName, groupConfigBean.getSessionType());

            }
        }

        return groupSessionTypes;
    }

    private Map<String, DroolsInstace> configGroupsContainers(DroolsConfigurationBean droolsConfigurationBean){

        Map<String, DroolsInstace> groupContainers = new HashMap<>();

        if (droolsConfigurationBean != null && droolsConfigurationBean.getIsEnabled()) {

            if (droolsConfigurationBean.getListGroups() == null){

                logger.warn("Drools Configuration is not found. Please, check your configuration if you want to use "
                        + "the send to drools action");

                return groupContainers;
            }

            KieServices ks = KieServices.Factory.get();

            for (String groupName : droolsConfigurationBean.getListGroups()){


                DroolsConfigurationGroupBean groupConfigBean = droolsConfigurationBean.getGroups().get(groupName);

                KieContainer groupContainer = null;

                try {
                    groupContainer = ks
                            .newKieContainer(
                                    ks.newReleaseId(groupConfigBean.getGroupId(), groupConfigBean.getArtifactId(),
                                            groupConfigBean.getVersion())
                            );
                }catch (Exception e){
                   logger.error("Error creating Drools KieContainer: " + e.getMessage());
                   logger.error("Please, check your Drools Configuration if you want to use the send to drools action"
                           + ".");
                }

                if (groupContainer != null) {

                    DroolsInstace instance = new DroolsInstace(groupContainer, groupConfigBean.getSessionName(),
                            groupConfigBean.getSessionType());

                    instance.setkScanner(ks.newKieScanner(groupContainer));
                    instance.getkScanner().start(groupConfigBean.getScanFrequency());

                    groupContainers.put(groupName, instance);

                } else {

                    if (logger.isDebugEnabled()){
                        logger.debug("It was not possible to create a KieContainer for group {}", groupName);
                    }
                }

            }

        }   else    {
            logger.info("Drools integration is not enabled");
        }

        return groupContainers;
    }

    public Map<String, DroolsInstace> getGroupContainers() {

        return groupContainers;
    }

    public DroolsInstace getGroupContainer(String groupName) {

        return groupContainers.get(groupName);
    }

    public Map<String, DroolsConfigurationGroupBean> getGroupConfigurations(){

        return groupConfigurations;
    }

    public DroolsConfigurationGroupBean getGroupConfiguration(String groupName) {

        return groupConfigurations.get(groupName);
    }

}
