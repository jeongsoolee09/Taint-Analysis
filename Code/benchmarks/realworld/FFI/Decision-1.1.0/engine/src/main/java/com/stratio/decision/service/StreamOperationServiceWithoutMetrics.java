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
package com.stratio.decision.service;

import com.stratio.decision.commons.constants.ColumnType;
import com.stratio.decision.commons.constants.EngineActionType;
import com.stratio.decision.commons.constants.STREAMING;
import com.stratio.decision.commons.constants.StreamAction;
import com.stratio.decision.commons.messages.ColumnNameTypeValue;
import com.stratio.decision.commons.messages.StratioStreamingMessage;
import com.stratio.decision.commons.messages.StreamQuery;
import com.stratio.decision.configuration.ConfigurationContext;
import com.stratio.decision.dao.StreamStatusDao;
import com.stratio.decision.drools.DroolsConnectionContainer;
import com.stratio.decision.exception.ServiceException;
import com.stratio.decision.functions.engine.BaseEngineAction;
import com.stratio.decision.functions.engine.DroolsEngineAction;
import com.stratio.decision.streams.QueryDTO;
import com.stratio.decision.streams.StreamStatusDTO;
import com.stratio.decision.utils.SiddhiUtils;

import org.kie.api.runtime.KieContainer;
import org.wso2.siddhi.core.SiddhiManager;
import org.wso2.siddhi.query.api.QueryFactory;
import org.wso2.siddhi.query.api.definition.Attribute;
import org.wso2.siddhi.query.api.definition.StreamDefinition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * Created by ajnavarro on 27/11/14.
 */
public class StreamOperationServiceWithoutMetrics {
    private final SiddhiManager siddhiManager;

    private final StreamStatusDao streamStatusDao;

    private final CallbackService callbackService;

    private  ConfigurationContext configurationContext;

    private  DroolsConnectionContainer droolsConnectionContainer;

    public StreamOperationServiceWithoutMetrics(SiddhiManager siddhiManager, StreamStatusDao streamStatusDao,
                                                CallbackService callbackService) {
        this.siddhiManager = siddhiManager;
        this.streamStatusDao = streamStatusDao;
        this.callbackService = callbackService;
    }


    public StreamOperationServiceWithoutMetrics(SiddhiManager siddhiManager, StreamStatusDao streamStatusDao,
            CallbackService callbackService, ConfigurationContext configurationContext) {
        this(siddhiManager, streamStatusDao,callbackService);
        this.configurationContext = configurationContext;
    }


    public StreamOperationServiceWithoutMetrics(SiddhiManager siddhiManager, StreamStatusDao streamStatusDao,
        CallbackService callbackService, DroolsConnectionContainer droolsConnectionContainer, ConfigurationContext configurationContext) {
        this(siddhiManager, streamStatusDao, callbackService, configurationContext);
        this.droolsConnectionContainer = droolsConnectionContainer;
    }


    public void createInternalStream(String streamName, List<ColumnNameTypeValue> columns) {
        StreamDefinition newStream = QueryFactory.createStreamDefinition().name(streamName);
        for (ColumnNameTypeValue column : columns) {
            newStream.attribute(column.getColumn(), getSiddhiType(column.getType()));
        }
        siddhiManager.defineStream(newStream);
        streamStatusDao.createInferredStream(streamName, columns);
     }

    public void createStream(String streamName, List<ColumnNameTypeValue> columns) {
        StreamDefinition newStream = QueryFactory.createStreamDefinition().name(streamName);
        if (columns!=null) {
            for (ColumnNameTypeValue column : columns) {
                newStream.attribute(column.getColumn(), getSiddhiType(column.getType()));
            }
        }
        siddhiManager.defineStream(newStream);
        streamStatusDao.create(streamName, columns);
    }

    public boolean streamExist(String streamName) {
        return streamStatusDao.get(streamName) != null ? true : false;
    }

    public boolean isUserDefined(String streamName) {
        StreamStatusDTO streamStatus = streamStatusDao.get(streamName);
        return streamStatus != null ? streamStatus.getUserDefined() : false;
    }

    public int enlargeStream(String streamName, List<ColumnNameTypeValue> columns) throws ServiceException {
//        int addedColumns = 0;
//        StreamDefinition streamMetaData = siddhiManager.getStreamDefinition(streamName);
//        for (ColumnNameTypeValue columnNameTypeValue : columns) {
//            if (!SiddhiUtils.columnAlreadyExistsInStream(columnNameTypeValue.getColumn(), streamMetaData)) {
//                addedColumns++;
//                streamMetaData.attribute(columnNameTypeValue.getColumn(), getSiddhiType(columnNameTypeValue.getType()));
//            } else {
//                throw new ServiceException(String.format("Alter stream error, Column %s already exists.",
//                        columnNameTypeValue.getColumn()));
//            }
//        }
//
//        return addedColumns;

        return enlargeStream(streamName, columns, true);
    }

    public int enlargeStream(String streamName, List<ColumnNameTypeValue> columns, Boolean raiseException) throws
            ServiceException {
        int addedColumns = 0;
        StreamDefinition streamMetaData = siddhiManager.getStreamDefinition(streamName);
        for (ColumnNameTypeValue columnNameTypeValue : columns) {
            if (!SiddhiUtils.columnAlreadyExistsInStream(columnNameTypeValue.getColumn(), streamMetaData)) {
                addedColumns++;
                // JPFM -- Updating the columns in streamStatusDao
                streamStatusDao.addColumn(streamName, columnNameTypeValue);
                streamMetaData.attribute(columnNameTypeValue.getColumn(), getSiddhiType(columnNameTypeValue.getType()));
            } else {
                if (raiseException) {
                    throw new ServiceException(String.format("Alter stream error, Column %s already "
                                    + "exists.",
                            columnNameTypeValue.getColumn()));
                }
            }
        }

        return addedColumns;
    }


    public void dropStream(String streamName) {

        Map<String, QueryDTO> attachedQueries = streamStatusDao.get(streamName).getAddedQueries();
        for (String queryId : attachedQueries.keySet()) {
            siddhiManager.removeQuery(queryId);
        }
        siddhiManager.removeStream(streamName);
        streamStatusDao.remove(streamName);
    }


    public String addQuery(String streamName, String queryString) {
        String queryId = siddhiManager.addQuery(queryString);
        streamStatusDao.addQuery(streamName, queryId, queryString);
        for (StreamDefinition streamDefinition : siddhiManager.getStreamDefinitions()) {
            // XXX refactor to obtain exactly siddhi inferred streams.
            streamStatusDao.createInferredStream(streamDefinition.getStreamId(),  castToColumnNameTypeValue(streamDefinition.getAttributeList()));
        }
        return queryId;
    }

    private List<ColumnNameTypeValue> castToColumnNameTypeValue(List<Attribute> attributeList) {
        List<ColumnNameTypeValue> result = new ArrayList<>();
        for (Attribute attribute : attributeList) {
            result.add(new ColumnNameTypeValue(attribute.getName(), getStreamingType(attribute.getType()), null));
        }
        return result;
    }

    public void removeQuery(String queryId, String streamName) {
        siddhiManager.removeQuery(queryId);
        streamStatusDao.removeQuery(streamName, queryId);
        for (Map.Entry<String, StreamStatusDTO> streamStatus : streamStatusDao.getAll().entrySet()) {
            String temporalStreamName = streamStatus.getKey();
            if (siddhiManager.getStreamDefinition(temporalStreamName) == null) {
                this.dropStream(temporalStreamName);
            }
        }
    }

    public boolean queryIdExists(String streamName, String queryId) {
        StreamStatusDTO streamStatus = streamStatusDao.get(streamName);
        if (streamStatus != null) {
            return streamStatus.getAddedQueries().containsKey(queryId);
        } else {
            return false;
        }
    }

    public boolean queryRawExists(String streamName, String queryRaw) {
        StreamStatusDTO streamStatus = streamStatusDao.get(streamName);
        if (streamStatus != null) {
            return streamStatus.getAddedQueries().containsValue(new QueryDTO(queryRaw));
        } else {
            return false;
        }
    }


    public Boolean columnExists(String streamName, String columnName){

        return streamStatusDao.existsColumnDefinition(streamName, columnName);

    }

    public void enableAction(String streamName, StreamAction action) {

        if (streamStatusDao.getEnabledActions(streamName).size() == 0) {
            String actionQueryId = siddhiManager.addQuery(QueryFactory.createQuery()
                    .from(QueryFactory.inputStream(streamName))
                    .insertInto(STREAMING.STATS_NAMES.SINK_STREAM_PREFIX.concat(streamName)));

            streamStatusDao.setActionQuery(streamName, actionQueryId);

            String groupId = null;

            if (configurationContext!=null && configurationContext.isClusteringEnabled()){
                groupId = configurationContext.getGroupId();
            }

            siddhiManager.addCallback(actionQueryId,
                    callbackService.add(streamName, streamStatusDao.getEnabledActions(streamName), groupId));
        }

        streamStatusDao.enableAction(streamName, action);
    }

    public void disableAction(String streamName, StreamAction action) {
        streamStatusDao.disableAction(streamName, action);

        if (streamStatusDao.getEnabledActions(streamName).size() == 0) {
            String actionQueryId = streamStatusDao.getActionQuery(streamName);
            if (actionQueryId != null) {
                siddhiManager.removeQuery(actionQueryId);
            }
            callbackService.remove(streamName);
        }
    }

    public boolean isActionEnabled(String streamName, StreamAction action) {
        return streamStatusDao.getEnabledActions(streamName).contains(action);
    }


    public void enableEngineAction(String streamName, EngineActionType engineActionType, Map<String, Object>
            engineActionParams) {
        this.enableEngineAction(streamName, engineActionType, engineActionParams, this);
    }

    protected void enableEngineAction(String streamName, EngineActionType engineActionType, Map<String, Object>
            engineActionParams,  StreamOperationServiceWithoutMetrics streamOperationService) {

        if ( !streamStatusDao.isEngineActionEnabled(streamName, engineActionType)){

            String engineActionQueryId = siddhiManager.addQuery(QueryFactory.createQuery()
                    .from(QueryFactory.inputStream(streamName))
                    .insertInto(STREAMING.STATS_NAMES.SINK_STREAM_PREFIX.concat(streamName)));

            BaseEngineAction engineAction = null;

            if (engineActionType == EngineActionType.FIRE_RULES) {

                engineAction = new DroolsEngineAction(droolsConnectionContainer, engineActionParams, siddhiManager, streamOperationService);

            }

            siddhiManager.addCallback(engineActionQueryId,
                    callbackService.addEngineCallback(streamName, engineActionType, engineAction));

            streamStatusDao.enableEngineAction(streamName, engineActionType, engineActionParams, engineActionQueryId);

        }


    }


    public void disableEngineAction(String streamName, EngineActionType engineActionType) {

        if ( streamStatusDao.isEngineActionEnabled(streamName, engineActionType)){

            String engineActionQueryId = streamStatusDao.getEngineActionQueryId(streamName, engineActionType);

            if (engineActionQueryId != null){

                siddhiManager.removeQuery(engineActionQueryId);
            }

            streamStatusDao.disableEngineAction(streamName, engineActionType);
            callbackService.removeEngineAction(streamName, engineActionType);

        }

    }

    public List<StratioStreamingMessage> list() {
        List<StratioStreamingMessage> result = new ArrayList<>();
        for (StreamDefinition streamDefinition : siddhiManager.getStreamDefinitions()) {
            if (suitableToList(streamDefinition.getStreamId())) {
                StratioStreamingMessage message = new StratioStreamingMessage();
                for (Attribute attribute : streamDefinition.getAttributeList()) {
                    message.addColumn(new ColumnNameTypeValue(attribute.getName(), this.getStreamingType(attribute
                            .getType()), null));
                }
                StreamStatusDTO streamStatus = streamStatusDao.get(streamDefinition.getStreamId());

                if (streamStatus != null) {
                    Map<String, QueryDTO> attachedQueries = streamStatus.getAddedQueries();

                    for (Map.Entry<String, QueryDTO> entry : attachedQueries.entrySet()) {
                        message.addQuery(new StreamQuery(entry.getKey(), entry.getValue().getQueryRaw()));
                    }
                    message.setUserDefined(streamStatus.getUserDefined());
                    message.setActiveActions(streamStatusDao.getEnabledActions(streamDefinition.getStreamId()));
                }

                message.setStreamName(streamDefinition.getStreamId());

                result.add(message);
            }
        }

        return result;
    }

    private boolean suitableToList(String streamName) {
        boolean startWithSinkPrefix = streamName.startsWith(STREAMING.STATS_NAMES.SINK_STREAM_PREFIX);
        boolean isAStatStream = Arrays.asList(STREAMING.STATS_NAMES.STATS_STREAMS).contains(streamName);

        return !startWithSinkPrefix && !isAStatStream;
    }


    public void send(String streamName, List<ColumnNameTypeValue> columns) throws ServiceException {
        try {
            siddhiManager.getInputHandler(streamName).send(
                    SiddhiUtils.getOrderedValues(siddhiManager.getStreamDefinition(streamName), columns));
        } catch (InterruptedException e) {
            throw new ServiceException(String.format("Error sending data to stream %s, column data: %s", streamName,
                    columns), e);
        }

    }

    private Attribute.Type getSiddhiType(ColumnType originalType) {
        switch (originalType) {
            case STRING:
                return Attribute.Type.STRING;
            case BOOLEAN:
                return Attribute.Type.BOOL;
            case DOUBLE:
                return Attribute.Type.DOUBLE;
            case INTEGER:
                return Attribute.Type.INT;
            case LONG:
                return Attribute.Type.LONG;
            case FLOAT:
                return Attribute.Type.FLOAT;
            default:
                throw new RuntimeException("Unsupported Column type: " + originalType);
        }
    }

    private ColumnType getStreamingType(Attribute.Type type) {
        switch (type) {
            case STRING:
                return ColumnType.STRING;
            case BOOL:
                return ColumnType.BOOLEAN;
            case DOUBLE:
                return ColumnType.DOUBLE;
            case INT:
                return ColumnType.INTEGER;
            case LONG:
                return ColumnType.LONG;
            case FLOAT:
                return ColumnType.FLOAT;
            default:
                throw new RuntimeException("Unsupported Column type: " + type);
        }
    }
}
