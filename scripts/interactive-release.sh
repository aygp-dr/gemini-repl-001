#!/bin/bash
# Interactive release helper for Gemini REPL

set -e

echo "=== Gemini REPL Release Helper ==="
echo ""

# Check for uncommitted changes
if ! git diff-index --quiet HEAD --; then
    echo "⚠️  Warning: You have uncommitted changes!"
    git status --short
    echo ""
    read -p "Do you want to continue anyway? (y/N) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "Aborting release process."
        exit 1
    fi
fi

# Show current version
CURRENT_VERSION=$(node -p "require('./package.json').version")
echo "Current version: $CURRENT_VERSION"
echo ""

# Ask for version type
echo "What type of release is this?"
echo "  1) Patch (bug fixes)     - $CURRENT_VERSION → $(npm version patch --no-git-tag-version --dry-run 2>/dev/null | tail -1)"
echo "  2) Minor (new features)  - $CURRENT_VERSION → $(npm version minor --no-git-tag-version --dry-run 2>/dev/null | tail -1)"
echo "  3) Major (breaking changes) - $CURRENT_VERSION → $(npm version major --no-git-tag-version --dry-run 2>/dev/null | tail -1)"
echo ""
read -p "Select release type (1-3): " choice

case $choice in
    1) VERSION_TYPE="patch" ;;
    2) VERSION_TYPE="minor" ;;
    3) VERSION_TYPE="major" ;;
    *) echo "Invalid choice"; exit 1 ;;
esac

# Show what will happen
echo ""
echo "This will:"
echo "  ✓ Run tests and linting"
echo "  ✓ Bump version ($VERSION_TYPE)"
echo "  ✓ Build the project"
echo "  ✓ Create release archive"
echo "  ✓ Generate release notes"
echo "  ✓ Create git tag"
echo ""

read -p "Continue with release? (y/N) " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Release cancelled."
    exit 0
fi

# Run the release
echo ""
echo "Starting release process..."
make release-$VERSION_TYPE

# Get new version
NEW_VERSION=$(node -p "require('./package.json').version")

# Show next steps
echo ""
echo "✅ Release v$NEW_VERSION prepared!"
echo ""
echo "Next steps:"
echo "  1. Review the release notes: releases/RELEASE-NOTES-v$NEW_VERSION.md"
echo "  2. Push the tag: git push origin v$NEW_VERSION"
echo "  3. Push the commit: git push"
echo ""
read -p "Create GitHub release now? (y/N) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo "Creating GitHub release..."
    gh release create "v$NEW_VERSION" \
        "releases/gemini-repl-v$NEW_VERSION.tar.gz" \
        --notes-file "releases/RELEASE-NOTES-v$NEW_VERSION.md" \
        --title "Gemini REPL v$NEW_VERSION"
    echo "✅ GitHub release created!"
fi