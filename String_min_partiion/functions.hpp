#include<vector>
#include<algorithm>
#include<iostream>
#include <boost/container_hash/hash.hpp>

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
  size_t current_variable;
  bool current_variable_good() {
    return (current_variable >= 0 && current_variable < ordered_variables.size());
  }
  void current_variable_reset() {
    current_variable = 0;
  }
  void current_variable_next() {
    ++current_variable;
  }
  variable_index_t current_variable_get() {
    return ordered_variables[current_variable];
  }
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


//state of inner node, two incidence strings
struct state_T {
  vector<bool> covered_s1, covered_s2;
  size_t level;
  size_t shortest_path;
  variable_index_t decision_index;
  state_T(const state_T& init) {
    covered_s1 = init.covered_s1;
    covered_s2 = init.covered_s2;
    level = init.level;
    shortest_path = init.shortest_path;
  }
  state_T(const state_T& init, const size_t& l) {
    covered_s1 = init.covered_s1;
    covered_s2 = init.covered_s2;
    shortest_path = init.shortest_path;
    level = l;
  }
  state_T(const state_T& init, const size_t& l, const size_t& sp) {
    covered_s1 = init.covered_s1;
    covered_s2 = init.covered_s2;
    level = l;
    shortest_path = sp;
  }
  state_T(const size_t& length) {
    covered_s1.clear();
    covered_s2.clear();
    covered_s1.resize(length, 1);
    covered_s2.resize(length, 1);
    shortest_path = 0;
    level = 0;
  }
  state_T() {
    covered_s1.clear();
    covered_s2.clear();
    shortest_path = 0;
    level = 0;
  };
  void print() const {
    std::cout << "State: l: " << level << " sp: " << shortest_path << "\n s1: ";
    for (bool b : covered_s1) {
      std::cout << b;
    }
    std::cout << "\n s2: ";
    for (bool b : covered_s2) {
      std::cout << b;
    }
    std::cout << std::endl;
  }
  size_t uncovovered_positions_count() const {
    size_t ret = 0;
    for (const bool& i : covered_s1) { ret += i; }
    return ret;
  }
  size_t get_shortest_path() const {
    return shortest_path + uncovovered_positions_count();
  }
};
inline bool operator==(const state_T& lhs, const state_T& rhs) {
  return (lhs.covered_s1 == rhs.covered_s1 && lhs.covered_s2 == rhs.covered_s2);
};
template<> struct std::hash<state_T>
{
  std::size_t operator()(state_T const& s) const noexcept
  {
    size_t seed = 0,
      h1 = std::hash<vector<bool>>{}(s.covered_s1),
      h2 = std::hash<vector<bool>>{}(s.covered_s2);
    boost::hash_combine(seed, h1);
    boost::hash_combine(seed, h2);
    return seed; // or use boost::hash_combine
  }
};

/*ostream& operator<<(ostream& os, const state_T& st) {
  os << "l: " << st.level << "/sp: " << st.shortest_path << "/s1: ";
  if (st.covered_s1.size() == 0 || st.covered_s2.size() == 0) { cout << "error"; return os; }
  for (bool b : st.covered_s1) {
    os << b;
  }
  os << "/s2: ";
  for (bool b : st.covered_s2) {
    os << b;
  }
  return os;
};*/

