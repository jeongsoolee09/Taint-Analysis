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
package com.stratio.decision.commons.avro;
@SuppressWarnings("all")
@org.apache.avro.specific.AvroGenerated
public class InsertMessage extends org.apache.avro.specific.SpecificRecordBase implements org.apache.avro.specific.SpecificRecord {
    private static final long serialVersionUID = 7664662872300091850L;
    public static final org.apache.avro.Schema SCHEMA$ = new org.apache.avro.Schema.Parser().parse("{\"type\":\"record\",\"name\":\"InsertMessage\",\"namespace\":\"com.stratio.decision.commons.avro\",\"fields\":[{\"name\":\"operation\",\"type\":[\"null\",\"string\"],\"default\":\"null\"},{\"name\":\"streamName\",\"type\":\"string\"},{\"name\":\"sessionId\",\"type\":[\"null\",\"string\"],\"default\":\"null\"},{\"name\":\"timestamp\",\"type\":[\"null\",\"long\"],\"default\":\"null\"},{\"name\":\"data\",\"type\":{\"type\":\"array\",\"items\":{\"type\":\"record\",\"name\":\"ColumnType\",\"fields\":[{\"name\":\"column\",\"type\":\"string\"},{\"name\":\"value\",\"type\":[\"null\",\"string\"],\"default\":\"null\"},{\"name\":\"type\",\"type\":[\"null\",\"string\"],\"default\":\"null\"}]}}},{\"name\":\"actions\",\"type\":[\"null\",{\"type\":\"array\",\"items\":{\"type\":\"enum\",\"name\":\"Action\",\"symbols\":[\"LISTEN\",\"SAVE_TO_CASSANDRA\",\"SAVE_TO_MONGO\",\"SAVE_TO_SOLR\",\"SAVE_TO_ELASTICSEARCH\"]}}],\"default\":\"null\"}]}");
    public static org.apache.avro.Schema getClassSchema() { return SCHEMA$; }
    @Deprecated public java.lang.CharSequence operation;
    @Deprecated public java.lang.CharSequence streamName;
    @Deprecated public java.lang.CharSequence sessionId;
    @Deprecated public java.lang.Long timestamp;
    @Deprecated public java.util.List<com.stratio.decision.commons.avro.ColumnType> data;
    @Deprecated public java.util.List<com.stratio.decision.commons.avro.Action> actions;

    /**
     * Default constructor.  Note that this does not initialize fields
     * to their default values from the schema.  If that is desired then
     * one should use <code>newBuilder()</code>.
     */
    public InsertMessage() {}

    /**
     * All-args constructor.
     */
    public InsertMessage(java.lang.CharSequence operation, java.lang.CharSequence streamName, java.lang.CharSequence sessionId, java.lang.Long timestamp, java.util.List<com.stratio.decision.commons.avro.ColumnType> data, java.util.List<com.stratio.decision.commons.avro.Action> actions) {
        this.operation = operation;
        this.streamName = streamName;
        this.sessionId = sessionId;
        this.timestamp = timestamp;
        this.data = data;
        this.actions = actions;
    }

    public org.apache.avro.Schema getSchema() { return SCHEMA$; }
    // Used by DatumWriter.  Applications should not call.
    public java.lang.Object get(int field$) {
        switch (field$) {
        case 0: return operation;
        case 1: return streamName;
        case 2: return sessionId;
        case 3: return timestamp;
        case 4: return data;
        case 5: return actions;
        default: throw new org.apache.avro.AvroRuntimeException("Bad index");
        }
    }
    // Used by DatumReader.  Applications should not call.
    @SuppressWarnings(value="unchecked")
    public void put(int field$, java.lang.Object value$) {
        switch (field$) {
        case 0: operation = (java.lang.CharSequence)value$; break;
        case 1: streamName = (java.lang.CharSequence)value$; break;
        case 2: sessionId = (java.lang.CharSequence)value$; break;
        case 3: timestamp = (java.lang.Long)value$; break;
        case 4: data = (java.util.List<com.stratio.decision.commons.avro.ColumnType>)value$; break;
        case 5: actions = (java.util.List<com.stratio.decision.commons.avro.Action>)value$; break;
        default: throw new org.apache.avro.AvroRuntimeException("Bad index");
        }
    }

    /**
     * Gets the value of the 'operation' field.
     */
    public java.lang.CharSequence getOperation() {
        return operation;
    }

    /**
     * Sets the value of the 'operation' field.
     * @param value the value to set.
     */
    public void setOperation(java.lang.CharSequence value) {
        this.operation = value;
    }

    /**
     * Gets the value of the 'streamName' field.
     */
    public java.lang.CharSequence getStreamName() {
        return streamName;
    }

    /**
     * Sets the value of the 'streamName' field.
     * @param value the value to set.
     */
    public void setStreamName(java.lang.CharSequence value) {
        this.streamName = value;
    }

    /**
     * Gets the value of the 'sessionId' field.
     */
    public java.lang.CharSequence getSessionId() {
        return sessionId;
    }

    /**
     * Sets the value of the 'sessionId' field.
     * @param value the value to set.
     */
    public void setSessionId(java.lang.CharSequence value) {
        this.sessionId = value;
    }

    /**
     * Gets the value of the 'timestamp' field.
     */
    public java.lang.Long getTimestamp() {
        return timestamp;
    }

    /**
     * Sets the value of the 'timestamp' field.
     * @param value the value to set.
     */
    public void setTimestamp(java.lang.Long value) {
        this.timestamp = value;
    }

    /**
     * Gets the value of the 'data' field.
     */
    public java.util.List<com.stratio.decision.commons.avro.ColumnType> getData() {
        return data;
    }

    /**
     * Sets the value of the 'data' field.
     * @param value the value to set.
     */
    public void setData(java.util.List<com.stratio.decision.commons.avro.ColumnType> value) {
        this.data = value;
    }

    /**
     * Gets the value of the 'actions' field.
     */
    public java.util.List<com.stratio.decision.commons.avro.Action> getActions() {
        return actions;
    }

    /**
     * Sets the value of the 'actions' field.
     * @param value the value to set.
     */
    public void setActions(java.util.List<com.stratio.decision.commons.avro.Action> value) {
        this.actions = value;
    }

    /**
     * Creates a new InsertMessage RecordBuilder.
     * @return A new InsertMessage RecordBuilder
     */
    public static com.stratio.decision.commons.avro.InsertMessage.Builder newBuilder() {
        return new com.stratio.decision.commons.avro.InsertMessage.Builder();
    }

    /**
     * Creates a new InsertMessage RecordBuilder by copying an existing Builder.
     * @param other The existing builder to copy.
     * @return A new InsertMessage RecordBuilder
     */
    public static com.stratio.decision.commons.avro.InsertMessage.Builder newBuilder(com.stratio.decision.commons.avro.InsertMessage.Builder other) {
        return new com.stratio.decision.commons.avro.InsertMessage.Builder(other);
    }

    /**
     * Creates a new InsertMessage RecordBuilder by copying an existing InsertMessage instance.
     * @param other The existing instance to copy.
     * @return A new InsertMessage RecordBuilder
     */
    public static com.stratio.decision.commons.avro.InsertMessage.Builder newBuilder(com.stratio.decision.commons.avro.InsertMessage other) {
        return new com.stratio.decision.commons.avro.InsertMessage.Builder(other);
    }

    /**
     * RecordBuilder for InsertMessage instances.
     */
    public static class Builder extends org.apache.avro.specific.SpecificRecordBuilderBase<InsertMessage>
            implements org.apache.avro.data.RecordBuilder<InsertMessage> {

        private java.lang.CharSequence operation;
        private java.lang.CharSequence streamName;
        private java.lang.CharSequence sessionId;
        private java.lang.Long timestamp;
        private java.util.List<com.stratio.decision.commons.avro.ColumnType> data;
        private java.util.List<com.stratio.decision.commons.avro.Action> actions;

        /** Creates a new Builder */
        private Builder() {
            super(com.stratio.decision.commons.avro.InsertMessage.SCHEMA$);
        }

        /**
         * Creates a Builder by copying an existing Builder.
         * @param other The existing Builder to copy.
         */
        private Builder(com.stratio.decision.commons.avro.InsertMessage.Builder other) {
            super(other);
            if (isValidValue(fields()[0], other.operation)) {
                this.operation = data().deepCopy(fields()[0].schema(), other.operation);
                fieldSetFlags()[0] = true;
            }
            if (isValidValue(fields()[1], other.streamName)) {
                this.streamName = data().deepCopy(fields()[1].schema(), other.streamName);
                fieldSetFlags()[1] = true;
            }
            if (isValidValue(fields()[2], other.sessionId)) {
                this.sessionId = data().deepCopy(fields()[2].schema(), other.sessionId);
                fieldSetFlags()[2] = true;
            }
            if (isValidValue(fields()[3], other.timestamp)) {
                this.timestamp = data().deepCopy(fields()[3].schema(), other.timestamp);
                fieldSetFlags()[3] = true;
            }
            if (isValidValue(fields()[4], other.data)) {
                this.data = data().deepCopy(fields()[4].schema(), other.data);
                fieldSetFlags()[4] = true;
            }
            if (isValidValue(fields()[5], other.actions)) {
                this.actions = data().deepCopy(fields()[5].schema(), other.actions);
                fieldSetFlags()[5] = true;
            }
        }

        /**
         * Creates a Builder by copying an existing InsertMessage instance
         * @param other The existing instance to copy.
         */
        private Builder(com.stratio.decision.commons.avro.InsertMessage other) {
            super(com.stratio.decision.commons.avro.InsertMessage.SCHEMA$);
            if (isValidValue(fields()[0], other.operation)) {
                this.operation = data().deepCopy(fields()[0].schema(), other.operation);
                fieldSetFlags()[0] = true;
            }
            if (isValidValue(fields()[1], other.streamName)) {
                this.streamName = data().deepCopy(fields()[1].schema(), other.streamName);
                fieldSetFlags()[1] = true;
            }
            if (isValidValue(fields()[2], other.sessionId)) {
                this.sessionId = data().deepCopy(fields()[2].schema(), other.sessionId);
                fieldSetFlags()[2] = true;
            }
            if (isValidValue(fields()[3], other.timestamp)) {
                this.timestamp = data().deepCopy(fields()[3].schema(), other.timestamp);
                fieldSetFlags()[3] = true;
            }
            if (isValidValue(fields()[4], other.data)) {
                this.data = data().deepCopy(fields()[4].schema(), other.data);
                fieldSetFlags()[4] = true;
            }
            if (isValidValue(fields()[5], other.actions)) {
                this.actions = data().deepCopy(fields()[5].schema(), other.actions);
                fieldSetFlags()[5] = true;
            }
        }

        /**
         * Gets the value of the 'operation' field.
         * @return The value.
         */
        public java.lang.CharSequence getOperation() {
            return operation;
        }

        /**
         * Sets the value of the 'operation' field.
         * @param value The value of 'operation'.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder setOperation(java.lang.CharSequence value) {
            validate(fields()[0], value);
            this.operation = value;
            fieldSetFlags()[0] = true;
            return this;
        }

        /**
         * Checks whether the 'operation' field has been set.
         * @return True if the 'operation' field has been set, false otherwise.
         */
        public boolean hasOperation() {
            return fieldSetFlags()[0];
        }


        /**
         * Clears the value of the 'operation' field.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder clearOperation() {
            operation = null;
            fieldSetFlags()[0] = false;
            return this;
        }

        /**
         * Gets the value of the 'streamName' field.
         * @return The value.
         */
        public java.lang.CharSequence getStreamName() {
            return streamName;
        }

        /**
         * Sets the value of the 'streamName' field.
         * @param value The value of 'streamName'.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder setStreamName(java.lang.CharSequence value) {
            validate(fields()[1], value);
            this.streamName = value;
            fieldSetFlags()[1] = true;
            return this;
        }

        /**
         * Checks whether the 'streamName' field has been set.
         * @return True if the 'streamName' field has been set, false otherwise.
         */
        public boolean hasStreamName() {
            return fieldSetFlags()[1];
        }


        /**
         * Clears the value of the 'streamName' field.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder clearStreamName() {
            streamName = null;
            fieldSetFlags()[1] = false;
            return this;
        }

        /**
         * Gets the value of the 'sessionId' field.
         * @return The value.
         */
        public java.lang.CharSequence getSessionId() {
            return sessionId;
        }

        /**
         * Sets the value of the 'sessionId' field.
         * @param value The value of 'sessionId'.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder setSessionId(java.lang.CharSequence value) {
            validate(fields()[2], value);
            this.sessionId = value;
            fieldSetFlags()[2] = true;
            return this;
        }

        /**
         * Checks whether the 'sessionId' field has been set.
         * @return True if the 'sessionId' field has been set, false otherwise.
         */
        public boolean hasSessionId() {
            return fieldSetFlags()[2];
        }


        /**
         * Clears the value of the 'sessionId' field.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder clearSessionId() {
            sessionId = null;
            fieldSetFlags()[2] = false;
            return this;
        }

        /**
         * Gets the value of the 'timestamp' field.
         * @return The value.
         */
        public java.lang.Long getTimestamp() {
            return timestamp;
        }

        /**
         * Sets the value of the 'timestamp' field.
         * @param value The value of 'timestamp'.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder setTimestamp(java.lang.Long value) {
            validate(fields()[3], value);
            this.timestamp = value;
            fieldSetFlags()[3] = true;
            return this;
        }

        /**
         * Checks whether the 'timestamp' field has been set.
         * @return True if the 'timestamp' field has been set, false otherwise.
         */
        public boolean hasTimestamp() {
            return fieldSetFlags()[3];
        }


        /**
         * Clears the value of the 'timestamp' field.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder clearTimestamp() {
            timestamp = null;
            fieldSetFlags()[3] = false;
            return this;
        }

        /**
         * Gets the value of the 'data' field.
         * @return The value.
         */
        public java.util.List<com.stratio.decision.commons.avro.ColumnType> getData() {
            return data;
        }

        /**
         * Sets the value of the 'data' field.
         * @param value The value of 'data'.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder setData(java.util.List<com.stratio.decision.commons.avro.ColumnType> value) {
            validate(fields()[4], value);
            this.data = value;
            fieldSetFlags()[4] = true;
            return this;
        }

        /**
         * Checks whether the 'data' field has been set.
         * @return True if the 'data' field has been set, false otherwise.
         */
        public boolean hasData() {
            return fieldSetFlags()[4];
        }


        /**
         * Clears the value of the 'data' field.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder clearData() {
            data = null;
            fieldSetFlags()[4] = false;
            return this;
        }

        /**
         * Gets the value of the 'actions' field.
         * @return The value.
         */
        public java.util.List<com.stratio.decision.commons.avro.Action> getActions() {
            return actions;
        }

        /**
         * Sets the value of the 'actions' field.
         * @param value The value of 'actions'.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder setActions(java.util.List<com.stratio.decision.commons.avro.Action> value) {
            validate(fields()[5], value);
            this.actions = value;
            fieldSetFlags()[5] = true;
            return this;
        }

        /**
         * Checks whether the 'actions' field has been set.
         * @return True if the 'actions' field has been set, false otherwise.
         */
        public boolean hasActions() {
            return fieldSetFlags()[5];
        }


        /**
         * Clears the value of the 'actions' field.
         * @return This builder.
         */
        public com.stratio.decision.commons.avro.InsertMessage.Builder clearActions() {
            actions = null;
            fieldSetFlags()[5] = false;
            return this;
        }

        @Override
        public InsertMessage build() {
            try {
                InsertMessage record = new InsertMessage();
                record.operation = fieldSetFlags()[0] ? this.operation : (java.lang.CharSequence) defaultValue(fields()[0]);
                record.streamName = fieldSetFlags()[1] ? this.streamName : (java.lang.CharSequence) defaultValue(fields()[1]);
                record.sessionId = fieldSetFlags()[2] ? this.sessionId : (java.lang.CharSequence) defaultValue(fields()[2]);
                record.timestamp = fieldSetFlags()[3] ? this.timestamp : (java.lang.Long) defaultValue(fields()[3]);
                record.data = fieldSetFlags()[4] ? this.data : (java.util.List<com.stratio.decision.commons.avro.ColumnType>) defaultValue(fields()[4]);
                record.actions = fieldSetFlags()[5] ? this.actions : (java.util.List<com.stratio.decision.commons.avro.Action>) defaultValue(fields()[5]);
                return record;
            } catch (Exception e) {
                throw new org.apache.avro.AvroRuntimeException(e);
            }
        }
    }

    private static final org.apache.avro.io.DatumWriter
            WRITER$ = new org.apache.avro.specific.SpecificDatumWriter(SCHEMA$);

    @Override public void writeExternal(java.io.ObjectOutput out)
            throws java.io.IOException {
        WRITER$.write(this, org.apache.avro.specific.SpecificData.getEncoder(out));
    }

    private static final org.apache.avro.io.DatumReader
            READER$ = new org.apache.avro.specific.SpecificDatumReader(SCHEMA$);

    @Override public void readExternal(java.io.ObjectInput in)
            throws java.io.IOException {
        READER$.read(this, org.apache.avro.specific.SpecificData.getDecoder(in));
    }

}