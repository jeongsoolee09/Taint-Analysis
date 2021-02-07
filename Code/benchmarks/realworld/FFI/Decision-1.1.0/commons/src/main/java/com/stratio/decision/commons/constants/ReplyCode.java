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
package com.stratio.decision.commons.constants;

public enum ReplyCode {
    OK(1, "Operation realized correctly."),
    KO_PARSER_ERROR(2, "Parser error."),
    KO_STREAM_ALREADY_EXISTS(3, "Stream already exists."),
    KO_STREAM_DOES_NOT_EXIST(4, "Stream does not exists."),
    KO_QUERY_ALREADY_EXISTS(5, "Query already exists."),
    KO_LISTENER_ALREADY_EXISTS(6, "Listener already exists."),
    KO_GENERAL_ERROR(7, "General error."),
    KO_COLUMN_ALREADY_EXISTS(8, "Column already exists."),
    KO_COLUMN_DOES_NOT_EXIST(9, "Column does not exists."),
    KO_LISTENER_DOES_NOT_EXIST(10, "Listener does not exists."),
    KO_QUERY_DOES_NOT_EXIST(11, "Query does not exists."),
    KO_STREAM_IS_NOT_USER_DEFINED(12, "Stream is not user defined."),
    KO_OUTPUTSTREAM_EXISTS_AND_DEFINITION_IS_DIFFERENT(
            13,
            "Output stream already exists and it´s definition is different."),
    KO_ACTION_ALREADY_ENABLED(14, "Action into stream already enabled."),
    KO_SOURCE_STREAM_DOES_NOT_EXIST(15, "Source stream in query does not exists."),
    KO_STREAM_OPERATION_NOT_ALLOWED(17, "Stream operation not allowed."),
    KO_NODE_NOT_REPLY(18, "Some node(s) of the cluster does not answer");

    private final Integer code;
    private final String message;

    private ReplyCode(int code, String message) {
        this.code = code;
        this.message = message;
    }

    public Integer getCode() {
        return code;
    }

    public String getMessage() {
        return message;
    }

}
