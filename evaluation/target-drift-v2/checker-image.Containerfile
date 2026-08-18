# The build context is produced by tools/prepare_target_drift_checker_image.py
# from the exact frozen workspace base commit and this digest-pinned image.
ARG LEAN_BASE_IMAGE=invalid.local/abrl-lean-base:unset
ARG WORKSPACE_BASE_COMMIT=UNSET
ARG SOURCE_FILES_AGGREGATE_SHA256=UNSET
ARG BUILD_INPUT_MANIFEST_SHA256=UNSET
ARG CHECKER_IMAGE_RECIPE_SHA256=UNSET
ARG BASE_IMAGE_DIGEST=UNSET
ARG LEAN_TOOLCHAIN_SHA256=UNSET
FROM ${LEAN_BASE_IMAGE} AS cache-builder

ARG WORKSPACE_BASE_COMMIT
ARG SOURCE_FILES_AGGREGATE_SHA256
ARG BUILD_INPUT_MANIFEST_SHA256
ARG CHECKER_IMAGE_RECIPE_SHA256
ARG BASE_IMAGE_DIGEST
ARG LEAN_TOOLCHAIN_SHA256
USER root
WORKDIR /build/base
COPY checker-base/ /build/base/
COPY checker-image-build-input.json /build/checker-image-build-input.json
COPY target_drift_checker_cache_manifest.py \
    /usr/local/lib/abrl/target_drift_checker_cache_manifest.py

# Network is permitted only while constructing this trusted image.  The
# resulting image is later executed with --network none and --pull never.
RUN lake exe cache get \
    && lake build BanditRLProof Tests \
    && python3 /usr/local/lib/abrl/target_drift_checker_cache_manifest.py create \
        --root /build/base/.lake --output /build/cache-manifest.json \
        --workspace-base-commit "${WORKSPACE_BASE_COMMIT}" \
        --source-files-aggregate-sha256 "${SOURCE_FILES_AGGREGATE_SHA256}" \
        --build-input-manifest-sha256 "${BUILD_INPUT_MANIFEST_SHA256}" \
        --checker-image-recipe-sha256 "${CHECKER_IMAGE_RECIPE_SHA256}" \
        --base-image-digest "${BASE_IMAGE_DIGEST}" \
        --lean-toolchain-sha256 "${LEAN_TOOLCHAIN_SHA256}" \
    && python3 /usr/local/lib/abrl/target_drift_checker_cache_manifest.py verify \
        --root /build/base/.lake --manifest /build/cache-manifest.json

FROM ${LEAN_BASE_IMAGE}

USER root
# The final image receives only the compiled cache and its byte-complete
# manifest, not the frozen source snapshot used in the builder stage.  The
# trusted controller copies this seed into each tmpfs replay; no host cache is
# mounted and the restricted worker never needs network access.
ARG ABRL_CHECKER_CACHE_ROOT=/opt/abrl-checker-cache/.lake
ARG ABRL_CHECKER_CACHE_MANIFEST=/opt/abrl-checker-cache/cache-manifest.json
COPY --from=cache-builder /build/base/.lake ${ABRL_CHECKER_CACHE_ROOT}
COPY --from=cache-builder /build/cache-manifest.json ${ABRL_CHECKER_CACHE_MANIFEST}
COPY --from=cache-builder /build/checker-image-build-input.json \
    /opt/abrl-checker-cache/build-input-manifest.json
RUN test -d "${ABRL_CHECKER_CACHE_ROOT}" \
    && test -f "${ABRL_CHECKER_CACHE_MANIFEST}" \
    && chmod -R a+rX /opt/abrl-checker-cache

RUN groupadd --gid 10001 abrl-controller \
    && useradd --uid 10001 --gid 10001 --no-create-home abrl-controller \
    && groupadd --gid 10002 abrl-worker \
    && useradd --uid 10002 --gid 10002 --no-create-home abrl-worker
COPY check_target_drift_container_controller.py /usr/local/bin/abrl-checker-controller
COPY check_target_drift_inner.py /usr/local/lib/abrl/check_target_drift_inner.py
RUN chmod 0555 /usr/local/bin/abrl-checker-controller \
    /usr/local/lib/abrl/check_target_drift_inner.py

USER 0:0
ENTRYPOINT ["/usr/local/bin/abrl-checker-controller"]
