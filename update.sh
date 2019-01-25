# Maybe we can make this git independent or safer?
# Upgrade redundancies likely exist. Shortcuts are purposefully avoided.

# Vars
FILE="$(realpath -s "$0")"
DIR="$(dirname $FILE)"
PKGDIR="$(dirname $DIR)"


cd "$DIR" 

# Update main package
echo "Updating Filters package."
git pull -q origin master 

echo "Now updating dependencies."


# CSS update
if [ -f "$PKGDIR/CSS/update.sh" ]
then
    sh "$PKGDIR/CSS/update.sh"
else
    echo "Could not find CSS, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/CSS
    echo "Installing CSS..."
    sh "$PKGDIR/CSS/install.sh"
fi

# TensorSpace update
if [ -f "$PKGDIR/TensorSpace/update.sh" ]
then
    sh "$PKGDIR/TensorSpace/update.sh"
else
    echo "Could not find TensorSpace, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/TensorSpace
    echo "Installing TensorSpace..."
    sh "$PKGDIR/TensorSpace/install.sh"
fi

echo "Successfully updated!"

