#include <iostream>
#include <cstring>
#include <fstream>
#include <set>

using namespace std;

const int dim = 50;

struct DFA {
    int nrStari = 0, m = 0, q0 = 0, k = 0, nrTranzitii = 0;
    set<int> stariFinale;
    int tranzitii[dim][dim] = {{}};
    char alfabet[dim] = "";
};

int cautCaracter(char c, char v[]) {
    for (int i = 0; i < strlen(v); ++i)
        if (v[i] == c)
            return i;
    return -1;
}

void initializare(DFA &a) {
    int i, j;
    for (i = 0; i < dim; ++i)
        for (j = 0; j < dim; ++j) {
            a.tranzitii[i][j] = -1;
        }
}

void construireMatriceAdiacenta(int adiacenta[][dim], const DFA &b) {
    int i, j;
    for (i = 0; i < b.nrStari; ++i)
        for (j = 0; j < b.nrStari; ++j)
            adiacenta[i][j] = 0;
    for (i = 0; i < b.nrStari; ++i)
        for (j = 0; j < b.m; ++j)
            if (b.tranzitii[i][j] != -1)
                adiacenta[i][b.tranzitii[i][j]] = 1;
}

bool deadend(const DFA &a, int adiacenta[dim][dim], int stare) {
    int vf, i, ok, stiva[dim], vizitat[a.nrStari];
    vf = 1;
    for (i = 0; i < a.nrStari; ++i)
        vizitat[i] = 0;
    stiva[vf] = stare;
    vizitat[stare] = 1;
    if (a.stariFinale.count(stare))
        return false;
    while (vf) {
        stare = stiva[vf];
        ok = 0;
        for (i = 0; i < a.nrStari && ok == 0; ++i)
            if (adiacenta[stare][i] && vizitat[i] == 0) {
                stiva[++vf] = i;
                vizitat[i] = 1;
                if (a.stariFinale.count(i))
                    return false;
                ok = 1;
            }
        if (ok == 0) --vf;
    }
    return true;
}

bool neaccesibil(const DFA &a, int adiacenta[dim][dim], int stare, int x) {
    int vf, i, ok, stiva[dim], vizitat[a.nrStari];
    vf = 1;
    for (i = 0; i < a.nrStari; ++i)
        vizitat[i] = 0;
    stiva[vf] = a.q0;
    vizitat[stare] = 1;
    while (vf) {
        stare = stiva[vf];
        ok = 0;
        for (i = 0; i < a.nrStari && ok == 0; ++i)
            if (adiacenta[stare][i] && vizitat[i] == 0) {
                stiva[++vf] = i;
                vizitat[i] = 1;
                if (i == x)
                    return false;
                ok = 1;
            }
        if (ok == 0) --vf;
    }
    return true;
}

void eliminare(DFA &b, int stare) {
    int i, j;
    for (i = 0; i < b.nrStari; ++i)
        for (j = 0; j < b.m; ++j)
            if (i == stare || j == stare)
                b.tranzitii[i][j] = -1;
}

void citire(DFA &a) {
    ifstream fin("DFA.in");
    int i, stare1, stare2;
    char tranzitie;
    fin >> a.nrStari >> a.m >> a.alfabet >> a.q0 >> a.k;
    for (i = 0; i < a.k; ++i) {
        int x;
        fin >> x;
        a.stariFinale.insert(x);
    }
    fin >> a.nrTranzitii;
    for (i = 0; i < a.nrTranzitii; ++i) {
        fin >> stare1 >> tranzitie >> stare2;
        a.tranzitii[stare1][cautCaracter(tranzitie, a.alfabet)] = stare2;
    }
}

void afisare(DFA a) {
    int i, j;
    set<int>::iterator k;
    bool afisat;
    cout << a.nrStari << "\n";
    cout << a.m << "\n";
    cout << a.alfabet << "\n";
    cout << a.q0 << "\n";
    cout << a.k << "\n";
    for (k = a.stariFinale.begin(); k != a.stariFinale.end(); ++k)
        cout << *k << " ";
    cout << "\n\n";
    for (i = 0; i < a.nrStari; ++i) {
        afisat = false;
        for (j = 0; j < a.m; ++j) {
            if (a.tranzitii[i][j] != -1) {
                cout << a.tranzitii[i][j] << " ";
                a.nrTranzitii++;
                afisat = true;
            }
        }
        if (afisat) cout << "\n";
    }
    cout << "\n" << a.nrTranzitii << "\n";
    for (i = 0; i < a.nrStari; ++i)
        for (j = 0; j < a.m; ++j)
            if (a.tranzitii[i][j] != -1)
                cout << i << " " << a.alfabet[j] << " " << a.tranzitii[i][j] << "\n";
}

void DFAtoDFAmin(const DFA &a, DFA &b) {
    bool echivalenta[a.nrStari][a.nrStari], modificare = true;
    int i, j, k, f[a.nrStari], nrStariCompuse = 0, adiacenta[dim][dim];
    set<int> stariCompuse[a.nrStari];
    for (i = 0; i < a.nrStari; ++i) {
        echivalenta[i][i] = true;
        f[i] = -1;
    }
    for (i = 0; i < a.nrStari; ++i)  //Construirea matricii de echivalenta
        for (j = 0; j < i; ++j)
            echivalenta[i][j] = echivalenta[j][i] = a.stariFinale.count(i) == a.stariFinale.count(j);
    while (modificare) {
        modificare = false;
        for (i = 1; i < a.nrStari; ++i)
            for (j = 0; j < i; ++j) {
                if (echivalenta[i][j]) {
                    for (k = 0; k < a.m; ++k)
                        if (!echivalenta[a.tranzitii[i][k]][a.tranzitii[j][k]]) {
                            modificare = true;
                            echivalenta[i][j] = echivalenta[j][i] = false;
                        }
                }
            }
    }
    for (i = 1; i < a.nrStari; ++i)  //Grupare stari + calcularea starii initiale si starilor finale
        for (j = 0; j < i; ++j)
            if (echivalenta[i][j]) {
                if (f[i] != -1) {
                    stariCompuse[f[i]].insert(j);
                    f[j] = f[i];
                    if (j == a.q0)
                        b.q0 = f[j];
                    if (a.stariFinale.count(j))
                        b.stariFinale.insert(f[j]);
                } else if (f[j] != -1) {
                    stariCompuse[f[j]].insert(i);
                    f[i] = f[j];
                    if (i == a.q0)
                        b.q0 = f[j];
                    if (a.stariFinale.count(i))
                        b.stariFinale.insert(f[i]);
                } else {
                    f[i] = f[j] = nrStariCompuse;
                    stariCompuse[nrStariCompuse].insert(i);
                    stariCompuse[nrStariCompuse++].insert(j);
                    if (j == a.q0)
                        b.q0 = f[j];
                    if (a.stariFinale.count(j))
                        b.stariFinale.insert(f[j]);
                    if (i == a.q0)
                        b.q0 = f[i];
                    if (a.stariFinale.count(i))
                        b.stariFinale.insert(f[i]);
                }
            }
    for (i = 0; i < a.nrStari; ++i)
        if (f[i] == -1) {
            stariCompuse[nrStariCompuse].insert(i);
            f[i] = nrStariCompuse;
            nrStariCompuse++;
        }
    b.nrStari = nrStariCompuse;
    b.m = a.m;
    strcpy(b.alfabet, a.alfabet);
    b.k = b.stariFinale.size();
    for (i = 0; i < b.nrStari; ++i)  //Calcularea functiei de tranzitie
        for (j = 0; j < b.m; ++j) {
            set<int>::iterator first;
            first = stariCompuse[i].begin();
            b.tranzitii[i][j] = f[a.tranzitii[*first][j]];
        }
    construireMatriceAdiacenta(adiacenta, b); //Eliminarea starilor deadend
    for (i = 0; i < b.nrStari; ++i)
        if (deadend(b, adiacenta, i)) {
            eliminare(b, i);
            b.nrStari--;
        }
    for (i = 0; i < b.nrStari; ++i)     //Eliminarea starilor inaccesibile
        if (i != b.q0 && neaccesibil(b, adiacenta, b.q0, i)) {
            eliminare(b, i);
            b.nrStari--;
        }
}

int main() {
    DFA a, b;
    citire(a);
    initializare(b);
    DFAtoDFAmin(a, b);
    afisare(b);
    return 0;
}
