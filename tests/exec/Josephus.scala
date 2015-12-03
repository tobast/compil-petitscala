
/** listes circulaires doublement chaînées */

class ListeC(v: Int) {

  var valeur: Int = v;
  var suivant: ListeC = this;
  var precedent: ListeC = this;

  /* insertion après un élément donnée */
  def insererApres(v: Int) {
    var e = new ListeC(v);
    e.suivant = suivant;
    suivant = e;
    e.suivant.precedent = e;
    e.precedent = this
  };

  /* suppression d'un élément donné */
  def supprimer() {
    precedent.suivant = suivant;
    suivant.precedent = precedent
  };

  /* affichage */
  def afficher() {
    var c = this;
    print(c.valeur);
    print(" ");
    c = c.suivant;
    while (c ne this) {
      print(c.valeur);
      print(" ");
      c = c.suivant
    };
    print("\n")
  }

}

/** Partie 3 : problème de Josephus */

class Josephus {

  /* construction de la liste circulaire 1,2,...,n;
   l'élément retourné est celui contenant 1 */
  def cercle(n: Int) : ListeC = {
    var l = new ListeC(1);
    var i = n;
    while (i >= 2) {
      l.insererApres(i);
      i = i-1
    };
    return l
  };

  /* jeu de Josephus */
  def josephus(n: Int, p: Int) : Int = {
    /* c est le joueur courant, 1 au départ */
    var c = cercle(n);

    /* tant qu'il reste plus d'un joueur */
    while (c ne c.suivant) {
      /* on élimine un joueur */
      var i = 1;
      while (i < p) { c = c.suivant; i = i + 1 };
      c.supprimer();
      c = c.suivant
    };
    return c.valeur
  }

}

/*** Tests */

object Main {

  def main(args: Array[String]) {
    var l = new ListeC(1);
    l.afficher();
    l.insererApres(3);
    l.afficher();
    l.insererApres(2);
    l.afficher();
    l.suivant.supprimer();
    l.afficher();

    var j = new Josephus();
    var c = j.cercle(7);
    c.afficher();

    if (j.josephus(7, 5) == 6 &&
	j.josephus(5, 5) == 2 &&
	j.josephus(5, 17) == 4 &&
	j.josephus(13, 2) == 11)
      print("ok\n")
  }

}
