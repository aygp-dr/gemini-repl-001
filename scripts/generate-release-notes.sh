#!/bin/bash
# Generate release notes from git history

set -e

if [ $# -ne 2 ]; then
    echo "Usage: $0 <old-version> <new-version>"
    exit 1
fi

OLD_VERSION=$1
NEW_VERSION=$2

echo "# Release Notes - v$NEW_VERSION"
echo ""
echo "## What's Changed"
echo ""

# Get commits since last version
if git rev-parse "v$OLD_VERSION" >/dev/null 2>&1; then
    # Group commits by type
    echo "### Features"
    git log "v$OLD_VERSION"..HEAD --pretty=format:"- %s" | grep "^- feat" || echo "- No new features"
    echo ""

    echo "### Bug Fixes"
    git log "v$OLD_VERSION"..HEAD --pretty=format:"- %s" | grep "^- fix" || echo "- No bug fixes"
    echo ""

    echo "### Enhancements"
    git log "v$OLD_VERSION"..HEAD --pretty=format:"- %s" | grep -E "^- (enhance|improve|perf)" || echo "- No enhancements"
    echo ""

    echo "### Documentation"
    git log "v$OLD_VERSION"..HEAD --pretty=format:"- %s" | grep "^- docs" || echo "- No documentation changes"
    echo ""

    echo "### Other Changes"
    git log "v$OLD_VERSION"..HEAD --pretty=format:"- %s" | grep -v -E "^- (feat|fix|enhance|improve|perf|docs|chore)" || echo "- No other changes"
    echo ""
else
    echo "This is the first release!"
    echo ""
    git log --pretty=format:"- %s" | head -20
    echo ""
fi

echo "## Statistics"
echo ""
echo "- Commits since last release: $(git rev-list "v$OLD_VERSION"..HEAD --count 2>/dev/null || git rev-list HEAD --count)"
echo "- Contributors: $(git log "v$OLD_VERSION"..HEAD --format='%an' 2>/dev/null | sort -u | wc -l || echo "1")"
echo ""

echo "## Installation"
echo ""
echo '```bash'
echo "tar -xzf gemini-repl-v$NEW_VERSION.tar.gz"
echo "cd v$NEW_VERSION"
echo "npm install"
echo "make run"
echo '```'
echo ""

echo "## Full Changelog"
echo ""
echo "https://github.com/aygp-dr/gemini-repl-001/compare/v$OLD_VERSION...v$NEW_VERSION"