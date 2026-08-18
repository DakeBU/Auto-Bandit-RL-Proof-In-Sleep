# Syntax and base image digest must be finalized before a production probe.
ARG LEAN_BASE_IMAGE=UNSET_DIGEST_PINNED_LEAN_IMAGE
FROM ${LEAN_BASE_IMAGE}

# The digest-pinned base image must already contain the complete, compiled Lake
# dependency closure used by the frozen workspace.  The trusted controller
# copies this seed into each tmpfs replay; no host cache is mounted and the
# restricted worker never needs network access.
ARG ABRL_CHECKER_CACHE_ROOT=/opt/abrl-checker-cache/.lake
ARG ABRL_CHECKER_CACHE_MANIFEST=/opt/abrl-checker-cache/cache-manifest.json
RUN test -d "${ABRL_CHECKER_CACHE_ROOT}/packages" \
    && test -f "${ABRL_CHECKER_CACHE_MANIFEST}" \
    && chmod -R a+rX /opt/abrl-checker-cache

USER root
RUN groupadd --gid 10001 abrl-controller \
    && useradd --uid 10001 --gid 10001 --no-create-home abrl-controller \
    && groupadd --gid 10002 abrl-worker \
    && useradd --uid 10002 --gid 10002 --no-create-home abrl-worker
COPY tools/check_target_drift_container_controller.py /usr/local/bin/abrl-checker-controller
COPY tools/check_target_drift_inner.py /usr/local/lib/abrl/check_target_drift_inner.py
RUN chmod 0555 /usr/local/bin/abrl-checker-controller \
    /usr/local/lib/abrl/check_target_drift_inner.py

USER 0:0
ENTRYPOINT ["/usr/local/bin/abrl-checker-controller"]
