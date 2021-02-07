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

import com.stratio.decision.callbacks.ActionControllerCallback;
import com.stratio.decision.callbacks.EngineActionCallback;
import com.stratio.decision.callbacks.StreamToActionBusCallback;
import com.stratio.decision.commons.constants.EngineActionType;
import com.stratio.decision.commons.constants.StreamAction;
import com.stratio.decision.commons.messages.StratioStreamingMessage;
import com.stratio.decision.functions.engine.BaseEngineAction;
import com.stratio.decision.serializer.Serializer;
import kafka.javaapi.producer.Producer;
import org.wso2.siddhi.core.event.Event;
import org.wso2.siddhi.core.query.output.callback.QueryCallback;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class CallbackService {

    private final Producer<String, String> producer;
    private final Producer<String, byte[]> avroProducer;
    private final Serializer<String, StratioStreamingMessage> kafkaToJavaSerializer;
    private final Serializer<StratioStreamingMessage, Event> javaToSiddhiSerializer;
    private final Serializer<StratioStreamingMessage, byte[]> javaToAvroSerializer;

    private final Map<String, ActionControllerCallback> referencedCallbacks;
    private final Map<String, EngineActionCallback> referencedEngineCallbacks;

    public CallbackService(Producer<String, String> producer,
            Producer<String, byte[]> avroProducer,
            Serializer<String, StratioStreamingMessage> kafkaToJavaSerializer,
            Serializer<StratioStreamingMessage, Event> javaToSiddhiSerializer,
            Serializer<StratioStreamingMessage, byte[]> javaToAvroSerializer) {
        this.producer = producer;
        this.avroProducer = avroProducer;
        this.kafkaToJavaSerializer = kafkaToJavaSerializer;
        this.javaToSiddhiSerializer = javaToSiddhiSerializer;
        this.javaToAvroSerializer = javaToAvroSerializer;
        this.referencedCallbacks = new HashMap<>();
        this.referencedEngineCallbacks = new HashMap<>();
    }

    public QueryCallback add(String streamName, Set<StreamAction> actions) {

        ActionControllerCallback callback = referencedCallbacks.get(streamName);

        if (callback == null) {
            callback = new StreamToActionBusCallback(actions, streamName, avroProducer,
                    javaToSiddhiSerializer, javaToAvroSerializer);
            referencedCallbacks.put(streamName, callback);
        }

        return callback;
    }

    public QueryCallback add(String streamName, Set<StreamAction> actions, String groupId) {

        ActionControllerCallback callback = referencedCallbacks.get(streamName);

        if (callback == null) {
            callback = new StreamToActionBusCallback(actions, streamName, avroProducer,
                    javaToSiddhiSerializer, javaToAvroSerializer, groupId);
            referencedCallbacks.put(streamName, callback);
        }

        return callback;
    }

    public void remove(String streamName) {
        referencedCallbacks.remove(streamName);
    }


    public QueryCallback addEngineCallback(String streamName, EngineActionType action, BaseEngineAction engineAction) {

        String key = streamName.concat("#").concat(action.toString());

        EngineActionCallback callback = referencedEngineCallbacks.get(key);

        if (callback == null) {

            callback = new EngineActionCallback(streamName, engineAction, producer, kafkaToJavaSerializer,
                    javaToSiddhiSerializer);

            referencedEngineCallbacks.put(key, callback);
        }

        return callback;
    }

    public void removeEngineAction(String streamName, EngineActionType action) {

        String key = streamName.concat("#").concat(action.toString());
        referencedEngineCallbacks.remove(key);
    }


}
