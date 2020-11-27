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


void or_states(state_T& s1, state_T& s2) {
  for (size_t i = 0; i < s1.covered_s1.size(); ++i) {
    s1.covered_s1[i] = s1.covered_s1[i] || s2.covered_s1[i];
    s1.covered_s2[i] = s1.covered_s2[i] || s2.covered_s2[i];
  }
}
void merge_edges(BDD_T& myBDD, const size_t& v1, const size_t& v2) {
  graph_traits<BDD_T>::out_edge_iterator ei, ei_end;
  property_map<BDD_T, edge_weight_t>::type decisions_map = get(edge_weight, myBDD);
  //cout << 1 << endl;
  for (boost::tie(ei, ei_end) = out_edges(v2, myBDD); ei != ei_end; ++ei) {
    if (ei->m_target == v1) continue;
    add_edge(v1, ei->m_target, decisions_map[*ei], myBDD);
    //cout << *ei << endl;
  }
  //cout << 2 << endl;
  graph_traits<BDD_T>::in_edge_iterator Iei, Iei_end;
  for (boost::tie(Iei, Iei_end) = in_edges(v2, myBDD); Iei != Iei_end; ++Iei) {
    if (Iei->m_source == v1) continue;
    add_edge(Iei->m_source, v1, decisions_map[*Iei], myBDD);
    //cout << *Iei << endl;
  }
  //cout << 3 << endl;
  clear_vertex(v2, myBDD);

}
void merge_nodes(BDD_T& myBDD, const size_t& v1, const size_t& v2) {
  or_states(myBDD[v1].state, myBDD[v2].state);
  merge_edges(myBDD, v1, v2);
};

void merge_clear_update(BDD_T& myBDD, std::unordered_map<state_T, size_t>& new_layer_hashed, const size_t& v1, const size_t& v2) {
  merge_edges(myBDD, v1, v2); //unify v1 and v2, remove selfloops
  size_t last_vertex_index = num_vertices(myBDD) - 1; //last vertex of bdd
  myBDD[v2].state = myBDD[last_vertex_index].state; //v2 is currently empty so can be fliped
  merge_edges(myBDD, v2, last_vertex_index); //switch last vertex with current vertex
  std::unordered_map<state_T, size_t>::iterator search_it = new_layer_hashed.find(myBDD[last_vertex_index].state);
  if (search_it != new_layer_hashed.end()) {
    search_it->second = v2; //update layer info if the vertex is present in last level
  }
  remove_vertex(last_vertex_index, myBDD); //this should be fast
}

void relax_layer(BDD_T& myBDD, vector<size_t>& current_layer, const size_t& restrict_width) {

};

void restrict_layer(BDD_T& myBDD, vector<size_t>& current_layer, const size_t& restrict_width) {
  std::sort(current_layer.begin(), current_layer.end(), [&myBDD](const size_t& x, const size_t& y) { return  myBDD[x].state.shortest_path < myBDD[y].state.shortest_path; });
  //current_layer.erase(current_layer.begin() + restrict_width / 2, current_layer.end() - restrict_width / 2);
  current_layer.resize(restrict_width);
}

void process_layer(BDD_T& myBDD, vector<size_t>& current_layer, variablesDB_t& variables, const size_t& restrict_width){
  std::unordered_map<state_T, size_t> new_layer_hashed;
  std::unordered_map<state_T, size_t>::iterator search_it;
  state_T state1, state0, can_be_covered_state;
  bool one_is_valid;
  size_t to_match;
  state_from_free_vars(can_be_covered_state, variables); //cover all positins which can be covered by free variables

  for (size_t procesed_node : current_layer){ // each node from current layer
    //check wheter state can be covered from procesed node
    myBDD[procesed_node].state.decision_index = variables.current_variable_get();
    state0 = myBDD[procesed_node].state;
    state1 = can_be_covered_state;
    and_states(state0, state1);
    if (state0.uncovovered_positions_count()) { continue; } //we have constant subtree

    state0 = myBDD[procesed_node].state; //state for decision 0
    state0.level++;
    state1 = myBDD[procesed_node].state; //state for decision 1
    state1.level++;
    one_is_valid = cover_positions(state1, variables.current_variable_get()); //if return false, than we have to unify procesed_node with a node x_i=0 
    search_it = new_layer_hashed.find(state0);
    
    if (search_it != new_layer_hashed.end()){
      to_match = search_it->second;
      add_decision_edge_upadate_node(myBDD, procesed_node, to_match, 0);
    } else {
      new_layer_hashed[state0] = add_new_decision(myBDD,procesed_node,0,state0);
    }
    if (one_is_valid){
      search_it = new_layer_hashed.find(state1);
      if (search_it != new_layer_hashed.end()){
        to_match = search_it->second;
        add_decision_edge_upadate_node(myBDD, procesed_node, to_match, 1);
      } else {
        new_layer_hashed[state1] = add_new_decision(myBDD,procesed_node,1,state1);
      }
    } else {
      if (procesed_node) {//zbdd operation for nonroot
        merge_clear_update(myBDD, new_layer_hashed, new_layer_hashed[state0], procesed_node);
        //merge_nodes(myBDD, new_layer_hashed[state0], procesed_node);
      }
    }
  }
  current_layer.clear();
  for (const pair<state_T, size_t>& pa: new_layer_hashed){
    current_layer.push_back(pa.second);
    if (restrict_width && restrict_width < current_layer.size()) {
      restrict_layer(myBDD, current_layer, restrict_width);
    }
  }
};




void unify_last_layer(BDD_T& myBDD, vector<size_t> last_layer){ //in last layer there is 1 true node an all of the others are uncovered
  size_t terminal = 0, best = myBDD[last_layer[0]].state.covered_s1.size();
  for (const size_t& node : last_layer){
    
    if ((myBDD[node].state.uncovovered_positions_count() == 0) && best > myBDD[node].state.shortest_path){
        cout << "Final node " << node << endl;
      terminal = node;
      
      best = myBDD[node].state.shortest_path;
    } 
  }
  cout << "Smallest cover partition is " << myBDD[terminal].state.shortest_path << endl;
};

size_t min_cover(const vector<size_t>& input1, const vector<size_t>& input2, const size_t& restrict_width=0){
  if (!check_input(input1,input2)){ return 0;}
  size_t input_len = input1.size();
  //init bdd with the root
  BDD_T myBDD;
  add_vertex(myBDD);
  myBDD[0].state = state_T(input_len);
  vector<size_t> current_layer;
  current_layer.push_back(0);
  variablesDB_t variables;
  variables.current_variable_reset();
  for (size_t k1 = 0; k1<input_len; ++k1){
    for (size_t k2 = 0; k2<input_len; ++k2){
      
      for (size_t t_len = 0 ; t_len < input_len - max<int>(k1,k2); ++t_len){
        if (input1[k1 + t_len] != input2[k2 + t_len]) { break; }
          //this is a valid block (k1,k2,t_len+1)
          variables.append_variable(variable_index_t(k1,k2,t_len,input1.size()));
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
    process_layer(myBDD, current_layer, variables, restrict_width);
    
    variables.current_variable_next();
    
  }
  //delete recursively all invalid vertices and unify others t
  //print_BDD(myBDD);  
  /*size_t last_level = myBDD[num_vertices(myBDD) - 1].state.level;
  cout << "Deleted: " << clear_BDD(myBDD) << endl;
  collect_ilevel_nodes(myBDD, current_layer, last_level);*/
  unify_last_layer(myBDD, current_layer);
  
  //print_BDD(myBDD);
  
  return input_len;
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
    input1 = vector<size_t>(input1.begin(), input1.begin()+60);
    input2 = input1;
    shuffle(input2.begin(),input2.end(), default_random_engine{});
    cout << (input1 == input2) << endl;
  //}
  input_stream.close();
  
  min_cover(input1,input2,3000);
  
  return 0;
}