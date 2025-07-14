#!/bin/bash
# Release script for Gemini REPL

set -e

# Check arguments
if [ $# -ne 1 ]; then
    echo "Usage: $0 [patch|minor|major]"
    exit 1
fi

VERSION_TYPE=$1

# Validate version type
if [[ ! "$VERSION_TYPE" =~ ^(patch|minor|major)$ ]]; then
    echo "Error: Version type must be patch, minor, or major"
    exit 1
fi

# Get current version
CURRENT_VERSION=$(node -p "require('./package.json').version")
echo "Current version: $CURRENT_VERSION"

# Bump version
echo "Bumping $VERSION_TYPE version..."
npm version $VERSION_TYPE --no-git-tag-version

# Get new version
NEW_VERSION=$(node -p "require('./package.json').version")
echo "New version: $NEW_VERSION"

# Build the project
echo "Building release..."
npm run build

# Create release directory
RELEASE_DIR="releases/v$NEW_VERSION"
mkdir -p $RELEASE_DIR

# Copy built files
echo "Copying files to release directory..."
cp -r target $RELEASE_DIR/
cp package.json $RELEASE_DIR/
cp package-lock.json $RELEASE_DIR/
cp README.org $RELEASE_DIR/
cp LICENSE $RELEASE_DIR/
cp -r resources $RELEASE_DIR/
cp -r scripts $RELEASE_DIR/
cp Makefile $RELEASE_DIR/
cp shadow-cljs.edn $RELEASE_DIR/
cp .env.example $RELEASE_DIR/

# Create release archive
echo "Creating release archive..."
cd releases
tar --exclude='*.env' --exclude='node_modules' -czf "gemini-repl-v$NEW_VERSION.tar.gz" "v$NEW_VERSION"
cd ..

# Generate release notes
echo "Generating release notes..."
./scripts/generate-release-notes.sh $CURRENT_VERSION $NEW_VERSION > "releases/RELEASE-NOTES-v$NEW_VERSION.md"

# Commit version bump
echo "Committing version bump..."
git add package.json package-lock.json
git commit -m "chore: bump version to $NEW_VERSION

Co-Authored-By: Claude <noreply@anthropic.com>"

# Create and push tag
echo "Creating git tag..."
git tag -a "v$NEW_VERSION" -m "Release v$NEW_VERSION"

# Show summary
echo ""
echo "Release v$NEW_VERSION prepared successfully!"
echo ""
echo "Archive created: releases/gemini-repl-v$NEW_VERSION.tar.gz"
echo "Release notes: releases/RELEASE-NOTES-v$NEW_VERSION.md"
echo ""
echo "To publish this release:"
echo "  1. Push the tag: git push origin v$NEW_VERSION"
echo "  2. Push the commit: git push"
echo "  3. Create GitHub release: gh release create v$NEW_VERSION releases/gemini-repl-v$NEW_VERSION.tar.gz --notes-file releases/RELEASE-NOTES-v$NEW_VERSION.md"