#include<vector>
#include<algorithm>
using namespace std;

struct variable_index_t {

  size_t k1, k2, t_length, n; //n is the size of input string
  void set(const size_t& pk1, const size_t& pk2, const size_t& pt_length, const size_t& pn) {
    k1 = pk1; k2 = pk2; t_length = pt_length; n = pn;
  }
  variable_index_t() { k1 = 0; k2 = 0; t_length = 0; n = 0; };
  variable_index_t(const variable_index_t& vit) {
    k1 = vit.k1; k2 = vit.k2; t_length = vit.t_length; n = vit.n;
  }
  variable_index_t(const size_t& pk1, const size_t& pk2, const size_t& pt_length, const size_t& pn) {
    k1 = pk1; k2 = pk2; t_length = pt_length; n = pn;
  }
  size_t get_index()const {
    return k1 + n + k2 + 2 * n + t_length; //this is index of variable, which correspnds to level
  };
};
inline bool operator==(const variable_index_t& lhs, const variable_index_t& rhs) {
  return lhs.get_index() == rhs.get_index();
};
inline bool operator<(const variable_index_t& lhs, const variable_index_t& rhs) {
  return lhs.get_index() < rhs.get_index();
};
inline bool operator>(const variable_index_t& lhs, const variable_index_t& rhs) {
  return lhs.get_index() > rhs.get_index();
};
inline bool operator<=(const variable_index_t& lhs, const variable_index_t& rhs) {
  return lhs.get_index() <= rhs.get_index();
};
inline bool operator>=(const variable_index_t& lhs, const variable_index_t& rhs) {
  return lhs.get_index() >= rhs.get_index();
};
inline bool operator!=(const variable_index_t& lhs, const variable_index_t& rhs) {
  return lhs.get_index() != rhs.get_index();
};

struct variablesDB_t {
  vector<variable_index_t> ordered_variables;
  void sort_vars() {
    sort(ordered_variables.begin(), ordered_variables.end());
  }
  void append_variable(const variable_index_t& new_var) {
    ordered_variables.push_back(new_var);
  }
  variable_index_t operator [](int i) const { return ordered_variables[i]; }
  variable_index_t& operator [](int i) { return ordered_variables[i]; }
  size_t size() { return ordered_variables.size(); }
};
