# The build context is prepared by tools/prepare_target_drift_agent_image.py.
# Its base is the already cache-complete, byte-attested checker image produced
# from the common pre-audit workspace.  No registry access occurs in this
# layer: the exact Codex package was verified before Docker received it.
ARG CHECKER_BASE_IMAGE=invalid.local/abrl-checker:unset
FROM ${CHECKER_BASE_IMAGE}

USER root
COPY codex/codex /opt/abrl-codex/codex
COPY codex/bwrap /opt/abrl-codex/codex-resources/bwrap
COPY codex/rg /opt/abrl-codex/path/rg
COPY codex/package.json /opt/abrl-codex/package.json
COPY target_drift_agent_pid1.py /usr/local/bin/abrl-agent-pid1
COPY codex_target_drift_adapter.py /usr/local/lib/abrl/codex_target_drift_adapter.py
COPY target_drift_agent_outer_controller.py /usr/local/lib/abrl/target_drift_agent_outer_controller.py
COPY target_drift_agent_outer_probe.py /usr/local/lib/abrl/target_drift_agent_outer_probe.py
COPY target_drift_agent_model_probe.py /usr/local/lib/abrl/target_drift_agent_model_probe.py

RUN chmod 0555 /opt/abrl-codex/codex \
        /opt/abrl-codex/codex-resources/bwrap \
        /opt/abrl-codex/path/rg \
        /usr/local/bin/abrl-agent-pid1 \
        /usr/local/lib/abrl/codex_target_drift_adapter.py \
        /usr/local/lib/abrl/target_drift_agent_outer_controller.py \
        /usr/local/lib/abrl/target_drift_agent_outer_probe.py \
        /usr/local/lib/abrl/target_drift_agent_model_probe.py \
    && chmod 0444 /opt/abrl-codex/package.json \
    && ln -sfn /opt/abrl-codex/codex /usr/local/bin/codex \
    && ln -sfn /opt/abrl-codex/path/rg /usr/local/bin/rg \
    && /usr/local/bin/codex --version

# PID 1 remains the trusted lifecycle controller.  The production launcher
# will give its evaluated child a numeric non-root uid and a tmpfs workspace;
# the result-free image probe uses the existing 10002 worker from the checker
# base solely to exercise the bundled Linux sandbox without provider access.
USER 0:0
ENTRYPOINT ["python3", "/usr/local/bin/abrl-agent-pid1"]
