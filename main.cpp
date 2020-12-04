#include <string>
#include <iostream>
#include <boost/config.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/copy.hpp>
#include <cassert>
#include <vector>
#include <map>
#include <fstream>
#include <algorithm>
#include <random>
#include <unordered_map>
#include "String_min_partiion/functions.hpp"

using namespace boost;
using namespace std;

struct VP {
  state_T state;
};

typedef property<edge_weight_t, bool> EdgeProperty;

typedef adjacency_list<vecS,vecS,bidirectionalS,VP, EdgeProperty> BDD_T;

struct restriction_t {
  size_t max_level_width;
  size_t best_known_result;
  size_t mode; //0 exact, 1 restrict, 2 relax
  restriction_t(const size_t& mw, const size_t& bkr, const size_t& m = 0) { max_level_width = mw; best_known_result = bkr; mode = m; }
  bool comparator_for_layer(BDD_T& myBDD, const size_t& x, const size_t& y) {
    return  myBDD[x].state.shortest_path < myBDD[y].state.shortest_path;
  }
  
};

void print_BDD(BDD_T& myBDD) {
  std::ofstream dmp;
  dmp.open("dmp.dot");
  boost::dynamic_properties dp;
  dp.property("node_id", get(boost::vertex_index, myBDD));
  dp.property("weight", get(boost::edge_weight, myBDD));
  write_graphviz_dp(dmp, myBDD, dp);
  dmp.close();
}

template <typename Graph>
struct non_zero_degree {
  non_zero_degree() { } // has to have a default constructor!

  non_zero_degree(const Graph& g) : g(&g) { }

  bool operator()(typename boost::graph_traits<Graph>::vertex_descriptor v) const
  {
    return degree(v, *g) != 0;
  }
  const Graph* g;
};
size_t clear_BDD(BDD_T& myBDD) {
  BDD_T newG;
  copy_graph(make_filtered_graph(myBDD, keep_all(), non_zero_degree<BDD_T>(myBDD)), newG);
  size_t reduction_size = num_vertices(myBDD) - num_vertices(newG);
  myBDD.clear();
  copy_graph(newG, myBDD);
  return reduction_size;
}
size_t collect_ilevel_nodes(const BDD_T& myBDD, vector<size_t>& gathered_level, const size_t& i_level) {
  gathered_level.clear();
  for (size_t i = 0; i < num_vertices(myBDD); ++i) {
    if (myBDD[i].state.level == i_level) {
      gathered_level.push_back(i);
    }
  }
  return gathered_level.size();
}

template <class Name>
class myEdgeWriter {
public:
     myEdgeWriter(Name _name) : name(_name) {}
     template <class VertexOrEdge>
     void operator()(std::ostream& out, const VertexOrEdge& v) const {
            out << "[x_i=\"" << name[v].decision << "\"]";
     }
private:
     Name name;
};template <class Name>
class myVertexWriter {
public:
     myVertexWriter(Name _name) : name(_name) {}
     template <class VertexOrEdge>
     void operator()(std::ostream& out, const VertexOrEdge& v) const {
            out << "[x_i=\"" << name[v].state << "\"]";
     }
private:
     Name name;
};

//function which checks whether both strings contains same multiset of letters
bool check_input(const vector<size_t>& input1, const vector<size_t>& input2){
  if (input1.size() == input2.size()){
    map<size_t, int> char_count;
    for (const size_t& c : input1){
      if (char_count.count(c) == 0){
        char_count[c]=0;
      }
      ++char_count[c];
    }
    for (char c : input2){ 
      if (char_count.count(c) == 0 || char_count[c]==0) return 0; //this is somehow ineffective, it could be optimized
      --char_count[c];
    }
    return 1;
  }
  return 0;
};

/*bool state_is_covered(const state_T& state){
  for (bool b : state.covered_s1){ //we have to check just one string as the other is already covered
    if (b) return 0;
  }
  return 1;
}*/




void state_from_free_vars(state_T& result, variablesDB_t& variables) {
  result = state_T(variables[0].n);
  for (size_t j = variables.current_variable; j < variables.size(); ++j) {
    for (size_t i = 0; i <= variables[j].t_length; ++i) {
      result.covered_s1[variables[j].k1 + i] = 0;
      result.covered_s2[variables[j].k2 + i] = 0;
    }
  }
}

void and_states(state_T& s1, state_T& s2) {
  for (size_t i = 0; i < s1.covered_s1.size(); ++i) {
    s1.covered_s1[i] = s1.covered_s1[i] && s2.covered_s1[i];
    s1.covered_s2[i] = s1.covered_s2[i] && s2.covered_s2[i];
  }
}
void or_states(state_T& s1, state_T& s2) {
  for (size_t i = 0; i < s1.covered_s1.size(); ++i) {
    s1.covered_s1[i] = s1.covered_s1[i] || s2.covered_s1[i];
    s1.covered_s2[i] = s1.covered_s2[i] || s2.covered_s2[i];
  }
}
size_t h_dist_states(const state_T& s1, const state_T& s2) {
  size_t h_dist_ret = 0;
  for (size_t i = 0; i < s1.covered_s1.size(); ++i) {
    h_dist_ret += (s1.covered_s1[i] != s2.covered_s1[i]);
    h_dist_ret += (s1.covered_s2[i] != s2.covered_s2[i]);
  }
  return h_dist_ret;
}

//returns new half of state corresponding to updatet target, which is an icidence vector, wherer target[i]=0 means it is already covered. clears target if it finds colision
bool cover_positions(state_T& target, const variable_index_t& var_state){ //const size_t& k1, const size_t& k2, const size_t& length){
  if (max<int>(var_state.k1, var_state.k2)+ var_state.t_length >= target.covered_s2.size()){ //bound check
    target.covered_s1.clear(); //can't be covered so retreat
      return 0;
  }
  for (size_t i = 0; i<= var_state.t_length; ++i){
    if (!target.covered_s1[var_state.k1+i] || !target.covered_s2[var_state.k2+i]){
      target.covered_s1.clear(); //can't be covered so retreat
      return 0;
    }
    target.covered_s1[var_state.k1+i]=0;
    target.covered_s2[var_state.k2+i]=0;
  }
  return 1;
};

size_t add_new_decision(BDD_T& myBDD, const size_t& decision_node, const bool& decision_value, const state_T& target_state){
  size_t target_node=num_vertices(myBDD);
  add_vertex(myBDD);
  myBDD[target_node].state = target_state;
  myBDD[target_node].state.level = myBDD[decision_node].state.level+1;
  myBDD[target_node].state.shortest_path = myBDD[decision_node].state.shortest_path + decision_value;
  add_edge(decision_node, target_node, decision_value , myBDD);
  //cout << myBDD[target_node].state << " added" << edl;
  return target_node;
};
void add_decision_edge_upadate_node(BDD_T& myBDD, const size_t& decision_node, size_t& target_node, const bool& decision_value){
   add_edge(decision_node, target_node, decision_value ,myBDD);
   myBDD[target_node].state.shortest_path = min <int>(myBDD[target_node].state.shortest_path, myBDD[decision_node].state.shortest_path+decision_value);
};


//add edges of v2 to v1 and clear all of v2 edges
void merge_edges(BDD_T& myBDD, const size_t& v1, const size_t& v2) {
  graph_traits<BDD_T>::out_edge_iterator ei, ei_end;
  property_map<BDD_T, edge_weight_t>::type decisions_map = get(edge_weight, myBDD);
  if (out_degree(v2, myBDD)) {
    for (boost::tie(ei, ei_end) = out_edges(v2, myBDD); ei != ei_end; ++ei) {
      if (ei->m_target == v1) continue;
      add_edge(v1, ei->m_target, decisions_map[*ei], myBDD);
    }
  }
  if (in_degree(v2, myBDD)){
    graph_traits<BDD_T>::in_edge_iterator Iei, Iei_end;
    for (boost::tie(Iei, Iei_end) = in_edges(v2, myBDD); Iei != Iei_end; ++Iei) {
      if (Iei->m_source == v1) continue;
      add_edge(Iei->m_source, v1, decisions_map[*Iei], myBDD);
    }
  }
}


//copy all edges to vertex to_remove from the last vertex and delete that vertex instead
void remove_vertex_by_switch_and_del(BDD_T& myBDD, const size_t& to_remove) {
  size_t last_vertex_index = num_vertices(myBDD) - 1; //last vertex of bdd
  clear_vertex(to_remove, myBDD);
  if (to_remove != last_vertex_index) {
    myBDD[to_remove].state = myBDD[last_vertex_index].state; //v2 is currently empty so can be fliped
    merge_edges(myBDD, to_remove, last_vertex_index); //switch last vertex with current vertex
    clear_vertex(last_vertex_index, myBDD);
  }
  remove_vertex(last_vertex_index, myBDD);
}


//makes or of the states (so we will cover all positions and we can use more variables to cover
void merge_nodes(BDD_T& myBDD, state_T& v1, state_T& v2) {
  and_states(v1, v2);
  v1.shortest_path = min<size_t>(v2.shortest_path, v2.shortest_path);
  //merge_edges(myBDD, v1, v2);
  //remove_vertex_by_switch_and_del(myBDD, v2);
};


//
void merge_clear_update(BDD_T& myBDD, std::unordered_map<state_T, size_t>& new_layer_hashed, const size_t& v1, const size_t& v2) {
  merge_edges(myBDD, v1, v2); //unify v1 and v2, remove selfloops
  remove_vertex_by_switch_and_del(myBDD, v2);  //remove vertex
  std::unordered_map<state_T, size_t>::iterator search_it = new_layer_hashed.find(myBDD[v2].state);
  if (search_it != new_layer_hashed.end()) {
    search_it->second = v2; //update layer info if the vertex is present in last level
  }
  
}

void relax_layer(BDD_T& myBDD, vector<state_T>& current_layer, const restriction_t& restrictions) {
  //sort them to use them in some order...shortest are first so we hopefully wont touch them
  //std::sort(current_layer.begin(), current_layer.end());
  //for (int i = 0; i < current_layer.size() - 1; ++i) { if (current_layer[i] == current_layer[i + 1]) cout << "PYCOOOO\n"; }
  
  //std::sort(current_layer.begin(), current_layer.end(), [&myBDD, &restrictions](const state_T& x, const state_T& y) { return x.shortest_path > y.shortest_path; });
  std::nth_element(current_layer.begin(), current_layer.begin() + restrictions.max_level_width, current_layer.end(), [&restrictions](const state_T& x, const state_T& y) {
    if (x.shortest_path > y.shortest_path) return x.uncovovered_positions_count() < y.uncovovered_positions_count();
    return x.shortest_path > y.shortest_path; });

  while (current_layer.size() > restrictions.max_level_width) {
    //cout << "pop " << current_layer.back() << " " << num_vertices(myBDD) <<  endl;
    size_t h_dist_best = current_layer[0].covered_s2.size(), h_dist_cur, index_of_best=0;
    for (int i = restrictions.max_level_width-1; i >=0 ; --i) {
      h_dist_cur = h_dist_states(current_layer[i], current_layer.back());
      if (h_dist_cur < h_dist_best) {
        h_dist_best = h_dist_cur;
        index_of_best = i;
      }
    }
    //cout << index_of_best << "=?=" << current_layer.size() - 1 << "/" << current_layer[index_of_best] << "=?=" << current_layer.back() << endl;
    merge_nodes(myBDD, current_layer[index_of_best], current_layer.back());
    /*for (int i = 0; i < current_layer.size(); ++i) {
      if (current_layer[i] == num_vertices(myBDD)) {
        current_layer[i] = current_layer.back();
      }
    }*/
    //clear_vertex(current_layer.back(), myBDD);
    //cout << "poped " << current_layer.back() << endl;
    current_layer.pop_back();
  }
};

void restrict_layer(BDD_T& myBDD, vector<state_T>& current_layer, const restriction_t& restrictions) {
  if (restrictions.max_level_width >= current_layer.size()) return;
  
  //std::sort(current_layer.begin(), current_layer.end(), [&myBDD, &restrictions](const state_T& x, const state_T& y) { return x.shortest_path > y.shortest_path;});
  std::nth_element(current_layer.begin(), current_layer.begin() + restrictions.max_level_width, current_layer.end(), [&restrictions](const state_T& x, const state_T& y) { 
    if (x.shortest_path > y.shortest_path) return x.uncovovered_positions_count() < y.uncovovered_positions_count();
    return x.shortest_path > y.shortest_path; });
  //std::sort(current_layer.begin(), current_layer.end(), [&myBDD](const size_t& x, const size_t& y) { return  myBDD[x].state.uncovovered_positions_count() < myBDD[y].state.uncovovered_positions_count(); });

  //current_layer.erase(current_layer.begin() + restrict_width / 2, current_layer.end() - restrict_width / 2);
  current_layer.resize(restrictions.max_level_width);
}

void process_layer(BDD_T& myBDD, vector<state_T>& current_layer, variablesDB_t& variables, const restriction_t& restrictions){
  std::unordered_map<state_T, size_t> new_layer_hashed;
  std::unordered_map<state_T, size_t>::iterator search_it;
  state_T state1, state0, can_be_covered_state;
  bool one_is_valid;
  size_t to_match;
  //state_from_free_vars(can_be_covered_state, variables); //cover all positins which can be covered by free variables

  for (state_T& procesed_node : current_layer){ // each node from current layer
    //check wheter state can be covered from procesed node
    procesed_node.decision_index = variables.current_variable_get();
    //state0 = procesed_node;
    //state1 = can_be_covered_state;
    //and_states(state0, state1);
    //if (state0.uncovovered_positions_count() || procesed_node.shortest_path > restrictions.best_known_result) { continue; } //we have constant subtree
    
    //set state x_i=0
    state0 = procesed_node; //state for decision 0
    state0.level++;
    search_it = new_layer_hashed.find(state0);
    if (search_it != new_layer_hashed.end()) {
      //to_match = search_it->second;
      search_it->second = min<size_t>(search_it->second, state0.shortest_path);
      //add_decision_edge_upadate_node(myBDD, procesed_node, to_match, 0);
    }
    else {
      new_layer_hashed[state0] = state0.shortest_path;// add_new_decision(myBDD, procesed_node, 0, state0);
    }
    //set state x_i=1 and check if it is possible
    state1 = procesed_node; //state for decision 1
    state1.level++;
    state1.shortest_path++;
    one_is_valid = cover_positions(state1, variables.current_variable_get()); //if return false, than we have to unify procesed_node with a node x_i=0 
    
    
    
    if (one_is_valid){
      search_it = new_layer_hashed.find(state1);
      if (search_it != new_layer_hashed.end()){
        //to_match = search_it->second;
        search_it->second = min<size_t>(search_it->second, procesed_node.shortest_path);
        //add_decision_edge_upadate_node(myBDD, procesed_node, to_match, 1);
      } else {
        new_layer_hashed[state1] = state1.shortest_path;// add_new_decision(myBDD, procesed_node, 1, state1);
      }
    } else {
      //if (procesed_node) {//zbdd operation for nonroot
        //merge_clear_update(myBDD, new_layer_hashed, new_layer_hashed[state0], procesed_node);
        //merge_nodes(myBDD, new_layer_hashed[state0], procesed_node);
      //}
    }
  }
  current_layer.clear();
  for (const pair<state_T, size_t>& pa: new_layer_hashed){
    current_layer.push_back(pa.first);
    current_layer.back().shortest_path = pa.second;
  }
  if (restrictions.max_level_width && restrictions.max_level_width < current_layer.size()) {
    if (restrictions.mode == 1) {
      restrict_layer(myBDD, current_layer, restrictions);
    } else if (restrictions.mode == 2) {
      relax_layer(myBDD, current_layer, restrictions);
    }
  }
};




//size_t unify_last_layer(BDD_T& myBDD, vector<size_t> last_layer){ //in last layer there is 1 true node an all of the others are uncovered
size_t unify_last_layer(BDD_T& myBDD, vector<state_T> last_layer) { //in last layer there is 1 true node an all of the others are uncovered
  state_T terminal=last_layer[0];
  size_t best = last_layer[0].covered_s1.size();
  vector<size_t> results;
  for (const state_T& node : last_layer){
    results.push_back(node.get_shortest_path());
    if (best > node.get_shortest_path()){
      
      terminal = node;
      
      best = node.get_shortest_path();
      //cout << "best update " << best << endl;
    }
  }
  //cout << "Smallest cover partition is " << best << endl;
  //sort(results.begin(), results.end());
  //for (auto c : results) cout << c << " ";
  //cout << endl;
  //terminal.print();
  return best;
};

size_t min_cover(const vector<size_t>& input1, const vector<size_t>& input2, const restriction_t& restrictions){
  if (!check_input(input1,input2)){ return 0;}
  size_t input_len = input1.size();
  //init bdd with the root
  BDD_T myBDD;
  add_vertex(myBDD);
  myBDD[0].state = state_T(input_len);
  //vector<size_t> current_layer;
  vector<state_T> current_layer;
  //current_layer.push_back(0);
  current_layer.push_back(state_T(input_len));
  variablesDB_t variables;
  variables.current_variable_reset();
  for (size_t k1 = 0; k1<input_len; ++k1){
    for (size_t k2 = 0; k2<input_len; ++k2){
      
      for (size_t t_len = 0 ; t_len < input_len - max<int>(k1,k2); ++t_len){
        if (input1[k1 + t_len] != input2[k2 + t_len] || t_len + 1  == input_len - max<int>(k1, k2)) { //break; 
          if (t_len + 1 == input_len - max<int>(k1, k2)) ++t_len;
          if (t_len > 0){
            --t_len;
            for (; t_len > 0; --t_len) {
              variables.append_variable(variable_index_t(k1, k2, t_len, input1.size()));
            }
          }
          break;
        }
          //this is a valid block (k1,k2,t_len+1)
          //if (t_len)
          //  variables.append_variable(variable_index_t(k1,k2,t_len,input1.size()));
          //process_layer(myBDD, current_layer, k1, k2, t_len, restrict_width);
        }
      
    }
  }
  
  while (variables.current_variable_good()) {
    cout << "Position " << variables.current_variable_get().k1 << ", " 
                        << variables.current_variable_get().k2 << " with block of length " 
                        << variables.current_variable_get().t_length << " and letter "
                        << input1[variables.current_variable_get().k1 + variables.current_variable_get().t_length] << " frontier size " 
                        << current_layer.size() << endl;
    process_layer(myBDD, current_layer, variables, restrictions);
    
    variables.current_variable_next();
    
  }
  //delete recursively all invalid vertices and unify others t
  //print_BDD(myBDD);  
  /*size_t last_level = myBDD[num_vertices(myBDD) - 1].state.level;
  cout << "Deleted: " << clear_BDD(myBDD) << endl;
  collect_ilevel_nodes(myBDD, current_layer, last_level);*/
  return unify_last_layer(myBDD, current_layer);
  
  //print_BDD(myBDD);
  
  //return input_len;
};

bool read_1_sequence(vector<size_t>& input1, ifstream& input_stream){
  if(!input_stream.good()){
      std::cerr << "Data loading error.\n";
      return 0;
  }
  std::string line, name, content;
  while( std::getline( input_stream, line ).good() ){
      if( line.empty() || line[0] == '>' ){ // Identifier marker
          if(!content.empty()) break;
          if( !name.empty() ){ // Print out what we read from the last entry
              std::cout << name << " : " << content << std::endl;
              name.clear();
          }
          if( !line.empty() ){
              name = line.substr(1);
          }
          content.clear();
      } else if( !name.empty() ){
          if( line.find(' ') != std::string::npos ){ // Invalid sequence--no spaces allowed
              name.clear();
              content.clear();
          } else {
              content += line;
          }
      }
  }
  if( !name.empty() ){ // Print out what we read from the last entry
      std::cout << name << " : " << content << std::endl;
      for (char c : content){
        input1.push_back((size_t)c);
      }
      return 1;
  } else return 0;
}

int main(int argc, char ** argv)
{
    vector<size_t> input1={1,2,3,4},
         input2={1,2,3,4};
         //ababbbabbab
  size_t input_size = input1.size();
  std::ifstream input_stream(".\\input\\random");
  //while (input_stream.good()){
    read_1_sequence(input1, input_stream);
    input1 = vector<size_t>(input1.begin(), input1.begin()+50);
    input2 = input1;
    shuffle(input2.begin(),input2.end(), default_random_engine{});
  //}
  input_stream.close();
  restriction_t restrictions(1000, input1.size(), 1);
  vector<size_t> results;
  //for (int i = 1; i < 10; ++i) {
    //restrictions.max_level_width = i * 1000;
    //restrictions.best_known_result = min_cover(input1, input2, restrictions);
    results.push_back(min_cover(input1, input2, restrictions));
    restrictions.mode = 2;
    results.push_back(min_cover(input1, input2, restrictions));
  //}
  for (auto r : results)
    cout << r << ", " ;
  cout << endl;
  //restrictions.mode = 2;
  //cout << restrictions.best_known_result << endl;
  //cout << (input1 == input2) << ":" << min_cover(input1, input2, restrictions) << "/" << restrictions.best_known_result << endl;
  
  return 0;
}