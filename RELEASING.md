# Releasing

1. **Create a release branch**:

   ```sh
   git checkout main
   git pull
   git checkout -b release/vX.Y.Z
   ```

2. **Update the version** in [Cargo.toml](Cargo.toml) under `[workspace.package]`:

   ```toml
   [workspace.package]
   version = "X.Y.Z"
   ```

3. **Regenerate the lockfile**:

   ```sh
   cargo generate-lockfile
   ```

4. **Commit and push the version bump**:

   ```sh
   git add Cargo.toml Cargo.lock
   git commit -m "Release vX.Y.Z"
   git push -u origin release/vX.Y.Z
   ```

5. **Open a pull request** into `main` and get it merged.

6. **Tag the release from `main`**:

   ```sh
   git checkout main
   git pull
   git tag vX.Y.Z
   git push origin vX.Y.Z
   ```

   The tag must match the pattern `vX.Y.Z` and the version in `Cargo.toml`.

7. **Monitor the release**. The [Release workflow](.github/workflows/release.yml) will automatically verify the tag matches the crate version and publish to [crates.io](https://crates.io/crates/esi).

   You can follow progress in the **Actions** tab of the repository.
