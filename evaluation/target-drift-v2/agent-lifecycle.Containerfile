ARG PYTHON_BASE_IMAGE
FROM ${PYTHON_BASE_IMAGE}

COPY tools/target_drift_agent_pid1.py /usr/local/bin/abrl-agent-pid1
RUN chmod 0555 /usr/local/bin/abrl-agent-pid1

USER 65532:65532
ENTRYPOINT ["python3", "/usr/local/bin/abrl-agent-pid1"]
