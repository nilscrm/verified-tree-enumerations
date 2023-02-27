section \<open>Labeled Trees\<close>

theory Labeled_Tree_Enumeration
  imports Tree_Graph Combinatorial_Enumeration_Algorithms.n_Sequences
begin

subsection \<open>Definition\<close>

definition labeled_trees :: "'a set \<Rightarrow> 'a pregraph set" where
  "labeled_trees V = {(V,E) | E. tree V E}"

subsection \<open>Algorithm\<close>

text \<open>Prüfer sequence to tree\<close>

definition prufer_sequences :: "'a list \<Rightarrow> 'a list set" where
  "prufer_sequences verts = n_sequences (set verts) (length verts - 2)"

fun prufer_seq_to_tree_edges :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list" where
  "prufer_seq_to_tree_edges [v,w] [] = [(v,w)]"
| "prufer_seq_to_tree_edges verts (a#seq) =
    (case find (\<lambda>x. x \<notin> set (a#seq)) verts of
      Some b \<Rightarrow> (a,b) # prufer_seq_to_tree_edges (remove1 b verts) seq)"

definition edges_of_edge_list :: "('a \<times> 'a) list \<Rightarrow> 'a edge set" where
  "edges_of_edge_list edge_list \<equiv> mk_edge ` set edge_list"

definition prufer_seq_to_tree :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a pregraph" where
  "prufer_seq_to_tree verts seq = (set verts, edges_of_edge_list (prufer_seq_to_tree_edges verts seq))"

definition labeled_tree_enum :: "'a list \<Rightarrow> 'a pregraph list" where
  "labeled_tree_enum verts = map (prufer_seq_to_tree verts) (n_sequence_enum verts (length verts - 2))"

(*definition labeled_tree_edges_enum :: "'a list \<Rightarrow> ('a \<times> 'a) list list" where
  "labeled_tree_edges_enum verts = map (prufer_seq_to_tree_edges verts) (n_sequence_enum verts (length verts - 2))"*)


subsection \<open>Correctness\<close>

text \<open>Tree to Prüfer sequence\<close>

definition incident_edges :: "'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "incident_edges v edge_list = filter (\<lambda>(u,w). u = v \<or> w = v) edge_list"

abbreviation "degree v edge_list \<equiv> length (incident_edges v edge_list)"

fun neighbor :: "'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a" where
  "neighbor v [] = undefined"
| "neighbor v ((u,w)#edges) = (if v = u then w else if v = w then u else neighbor v edges)"

definition remove_vertex :: "'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "remove_vertex v = filter (\<lambda>(u,w). u \<noteq> v \<and> w \<noteq> v)"

lemma find_in_list[termination_simp]: "find P verts = Some v \<Longrightarrow> v \<in> set verts"
  by (metis find_Some_iff nth_mem)

lemma [termination_simp]: "find P verts = Some v \<Longrightarrow> length verts - Suc 0 < length verts"
  by (meson diff_Suc_less length_pos_if_in_set find_in_list)

fun tree_to_prufer_seq :: "'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a list" where
  "tree_to_prufer_seq verts [] = undefined"
| "tree_to_prufer_seq verts [(u,w)] = []"
| "tree_to_prufer_seq verts edges =
    (case find (\<lambda>v. degree v edges = 1) verts of
      Some leaf \<Rightarrow> neighbor leaf edges # tree_to_prufer_seq (remove1 leaf verts) (remove_vertex leaf edges))"

lemma remove_vertex: "edges_of_edge_list (remove_vertex v edge_list) = {e \<in> edges_of_edge_list edge_list. v \<notin> e}"
  unfolding remove_vertex_def by (auto simp: edges_of_edge_list_def)

lemma neighbor_ne: "\<forall>(u,w)\<in>set edge_list. u \<noteq> w \<Longrightarrow> degree v edge_list \<ge> 1 \<Longrightarrow> neighbor v edge_list \<noteq> v"
  unfolding incident_edges_def by (induction edge_list rule: neighbor.induct) auto

lemma degree_remove_vertex_0[simp]: "degree v (remove_vertex v edge_list) = 0"
  unfolding incident_edges_def remove_vertex_def
  by (smt (verit, best) filter_False list.size(3) mem_Collect_eq set_filter split_def)

lemma degree_0_remove_vertex:
  assumes degree_0: "degree v edge_list = 0"
  shows "remove_vertex v edge_list = edge_list"
proof-
  have "\<forall>(u,w) \<in> set edge_list. u \<noteq> v \<and> w \<noteq> v" using degree_0 unfolding incident_edges_def
    by (simp add: filter_empty_conv split_def)
  then show ?thesis unfolding remove_vertex_def by simp
qed

lemma degree_length_filter: "degree v edge_list = length (filter (\<lambda>e. v \<in> e) (map mk_edge edge_list))"
proof-
  have "(\<lambda>(u, w). u = v \<or> w = v) = (\<in>) v \<circ> mk_edge" by auto
  then have 1: "map mk_edge (filter (\<lambda>(u, w). u = v \<or> w = v) edge_list) = filter ((\<in>) v) (map mk_edge edge_list)" using filter_map by metis
  have "length (filter (\<lambda>(u, w). u = v \<or> w = v) edge_list) = length (map mk_edge (filter (\<lambda>(u, w). u = v \<or> w = v) edge_list))" by simp
  then show ?thesis unfolding incident_edges_def using 1 by argo
qed

lemma degree_neighbor_remove_vertex: "degree v edge_list = 1 \<Longrightarrow> Suc (degree (neighbor v edge_list) (remove_vertex v edge_list)) = degree (neighbor v edge_list) edge_list"
proof (induction v edge_list rule: neighbor.induct)
  case (1 v)
  then show ?case unfolding incident_edges_def remove_vertex_def by simp
next
  case (2 v u w edges)
  assume degree_1: "degree v ((u, w) # edges) = 1"
  consider "u = v \<and> w = v" | "u \<noteq> v \<and> w = v" | "u = v \<and> w \<noteq> v" | "u \<noteq> v \<and> w \<noteq> v" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis using 2 by simp
  next
    case 2
    then have "degree v edges = 0" using degree_1 unfolding incident_edges_def by auto
    then show ?thesis using 2 degree_0_remove_vertex unfolding remove_vertex_def incident_edges_def by fastforce
  next
    case 3
    then have "degree v edges = 0" using degree_1 unfolding incident_edges_def by auto
    then show ?thesis using 3 degree_0_remove_vertex unfolding remove_vertex_def incident_edges_def by fastforce
  next
    case 4
    then have "degree v edges = 1" using 2(2) unfolding incident_edges_def by auto
    then show ?thesis using 4 "2.IH" unfolding remove_vertex_def incident_edges_def by auto
  qed
qed

lemma distinct_remove_vertex[simp]: "distinct (map mk_edge edge_list) \<Longrightarrow> distinct (map mk_edge (remove_vertex leaf edge_list))"
  unfolding remove_vertex_def using distinct_map_filter by fast

lemma neighbor_edge_in_edges: "degree v edge_list \<ge> 1 \<Longrightarrow> {neighbor v edge_list, v} \<in> edges_of_edge_list edge_list"
  unfolding incident_edges_def edges_of_edge_list_def by (induction v edge_list rule: neighbor.induct) auto

lemma insert_remove_leaf:
  assumes degree_leaf: "degree leaf edge_list = 1"
    shows "insert {neighbor leaf edge_list, leaf} (edges_of_edge_list (remove_vertex leaf edge_list)) = edges_of_edge_list edge_list"
proof-
  let ?leaf_edges = "filter (\<lambda>(u,w). u = leaf \<or> w = leaf) edge_list"
  have length_leaf_edges: "length ?leaf_edges = 1" using degree_leaf unfolding incident_edges_def by simp
  have "{neighbor leaf edge_list, leaf} \<in> edges_of_edge_list edge_list" using neighbor_edge_in_edges degree_leaf by force
  then have "(neighbor leaf edge_list, leaf) \<in> set edge_list \<or> (leaf, neighbor leaf edge_list) \<in> set edge_list" by (simp add: edges_of_edge_list_def in_mk_uedge_img_iff)
  then have "(neighbor leaf edge_list, leaf) \<in> set ?leaf_edges \<or> (leaf, neighbor leaf edge_list) \<in> set ?leaf_edges" by simp
  then have "?leaf_edges = [(neighbor leaf edge_list, leaf)] \<or> ?leaf_edges = [(leaf, neighbor leaf edge_list)]" using length_leaf_edges
    by (smt (verit) One_nat_def empty_iff empty_set length_0_conv length_Suc_conv list.inject list.set_cases)
  then have leaf_edges: "edges_of_edge_list ?leaf_edges = {{neighbor leaf edge_list, leaf}}" unfolding edges_of_edge_list_def by fastforce

  have "edges_of_edge_list edge_list = edges_of_edge_list ?leaf_edges \<union> edges_of_edge_list (remove_vertex leaf edge_list)" unfolding remove_vertex_def edges_of_edge_list_def by auto
  then show ?thesis using leaf_edges by auto
qed

lemma find_Some: "find P xs = Some x \<Longrightarrow> P x"
  by (metis find_Some_iff)

definition verts_of_edges :: "('a \<times> 'a) list \<Rightarrow> 'a set" where
  "verts_of_edges edges = {v | v e. v \<in> e \<and> e \<in> edges_of_edge_list edges}"


locale prufer_seq_to_tree_context =
  fixes verts :: "'a list"
  assumes verts_length: "length verts \<ge> 2"
    and distinct_verts: "distinct verts"
begin

lemma card_verts: "card (set verts) \<ge> 2"
  using verts_length distinct_verts distinct_card by fastforce

lemma length_gt_find_not_in_ys:
  assumes "length xs > length ys"
    and "distinct xs"
  shows "\<exists>x. find (\<lambda>x. x \<notin> set ys) xs = Some x"
proof-
  have "card (set xs) > card (set ys)"
    by (metis assms card_length distinct_card le_neq_implies_less order_less_trans)
  then have "\<exists>x\<in>set xs. x \<notin> set ys"
    by (meson finite_set card_subset_not_gt_card subsetI)
  then show ?thesis by (metis find_None_iff2 not_Some_eq)
qed

lemma obtain_b_prufer_seq_to_tree_edges:
  assumes "(a # seq) \<in> prufer_sequences verts"
  obtains b
  where "find (\<lambda>x. x \<notin> set (a # seq)) verts = Some b"
    and "b \<in> set verts"
    and "b \<notin> set (a # seq)"
    and "seq \<in> prufer_sequences (remove1 b verts)"
    and "length (remove1 b verts) \<ge> 2"
    and "distinct (remove1 b verts)"
proof-
  obtain b where b_find: "find (\<lambda>x. x \<notin> set (a#seq)) verts = Some b"
    using assms length_gt_find_not_in_ys[of "a#seq" verts] distinct_verts
    unfolding prufer_sequences_def n_sequences_def
    by fastforce
  have b_in_verts: "b \<in> set verts" using b_find
    by (metis find_Some_iff nth_mem)
  have b_not_in_seq: "b \<notin> set (a#seq)" using b_find
    by (metis find_Some_iff)
  have seq_prufer_verts': "seq \<in> prufer_sequences (remove1 b verts)"
    using assms b_in_verts set_remove1_eq verts_length b_not_in_seq distinct_verts
    unfolding prufer_sequences_def n_sequences_def
    by (auto simp: length_remove1)
  have "length verts \<ge> 3" using assms unfolding prufer_sequences_def n_sequences_def by auto
  then have length_verts': "length (remove1 b verts) \<ge> 2" by (auto simp: length_remove1)
  have distinct: "distinct (remove1 b verts)" using distinct_remove1 assms distinct_verts by fast
  from b_find b_in_verts b_not_in_seq seq_prufer_verts' length_verts' distinct show ?thesis ..
qed

lemma verts_of_edges_prufer_to_tree[simp]:
  "seq \<in> prufer_sequences verts \<Longrightarrow>
    verts_of_edges (prufer_seq_to_tree_edges verts seq) = set verts"
  using verts_length distinct_verts
proof (induction verts seq rule: prufer_seq_to_tree_edges.induct)
  case (1 v w)
  then show ?case unfolding verts_of_edges_def edges_of_edge_list_def by auto
next
  case (2 verts a seq)
  then interpret contxt: prufer_seq_to_tree_context verts by unfold_locales
  obtain b
    where b_find: "find (\<lambda>x. x \<notin> set (a # seq)) verts = Some b"
      and seq_in_verts': "seq \<in> prufer_sequences (remove1 b verts)"
      and len_verts': "2 \<le> length (remove1 b verts)"
      and distinct_verts': "distinct (remove1 b verts)"
      and b_in_verts: "b \<in> set verts"
    using contxt.obtain_b_prufer_seq_to_tree_edges 2 by metis
  then have "verts_of_edges (prufer_seq_to_tree_edges verts (a # seq))
    = verts_of_edges ((a,b) # prufer_seq_to_tree_edges (remove1 b verts) seq)"
    by auto
  also have "\<dots> = {a,b} \<union> verts_of_edges (prufer_seq_to_tree_edges (remove1 b verts) seq)"
    unfolding verts_of_edges_def edges_of_edge_list_def by auto
  also have "\<dots> = {a,b} \<union> (set verts - {b})" using "2.IH"[OF b_find seq_in_verts' len_verts' distinct_verts'] b_in_verts by fastforce
  also have "\<dots> = set verts" using "2.prems"(1) b_in_verts unfolding prufer_sequences_def n_sequences_def by auto
  finally show ?case .
qed (auto simp: prufer_sequences_def n_sequences_def)

lemma prufer_seq_to_tree_edges_tree:
  assumes "seq \<in> prufer_sequences verts"
  shows "tree (verts_of_edges (prufer_seq_to_tree_edges verts seq)) (edges_of_edge_list (prufer_seq_to_tree_edges verts seq))"
    (is "tree (?V verts seq) (?E verts seq)")
  using assms verts_length distinct_verts
proof(induction verts seq rule: prufer_seq_to_tree_edges.induct)
  case (1 v w)
  have [simp]: "verts_of_edges [(v,w)] = {v,w}"
    unfolding verts_of_edges_def edges_of_edge_list_def using 1 by auto

  interpret ulgraph "?V [v,w] []" "?E [v,w] []"
    by (unfold_locales, auto simp: card_insert_if verts_of_edges_def edges_of_edge_list_def)
  
  have "connecting_path v w [v,w]"
    unfolding connecting_path_def  is_gen_path_def is_walk_def
    by (auto simp: verts_of_edges_def edges_of_edge_list_def)
  then have "vert_connected v w" "vert_connected w v"
    unfolding vert_connected_def using connecting_path_rev by auto
  then have connected: "is_connected_set (?V [v,w] [])"
    unfolding is_connected_set_def using vert_connected_id by auto
  then have fin_connected_ulgraph: "fin_connected_ulgraph (?V [v,w] []) (?E [v,w] [])"
    using 1 unfolding verts_of_edges_def edges_of_edge_list_def by (unfold_locales, auto)

  then show ?case using fin_connected_ulgraph 1 unfolding edges_of_edge_list_def by (auto intro: card_E_treeI)
next
  case (2 verts a seq)
  then interpret contxt: prufer_seq_to_tree_context verts by unfold_locales
  obtain b
    where b_find: "find (\<lambda>x. x \<notin> set (a # seq)) verts = Some b"
      and b_in_verts: "b \<in> set verts"
      and b_notin_seq: "b \<notin> set (a # seq)"
      and seq_pruf_verts': "seq \<in> prufer_sequences (remove1 b verts)"
      and length_verts': "length (remove1 b verts) \<ge> 2"
      and distinct_verts': "distinct (remove1 b verts)"
    using contxt.obtain_b_prufer_seq_to_tree_edges 2 by metis
  then interpret tree': tree "?V (remove1 b verts) seq" "?E (remove1 b verts) seq"
    using 2 seq_pruf_verts' distinct_remove1 b_find b_in_verts by auto

  interpret contxt': prufer_seq_to_tree_context "remove1 b verts" using length_verts' distinct_verts' by unfold_locales

  have V'[simp]: "?V (remove1 b verts) seq = set verts - {b}"
    using contxt'.verts_of_edges_prufer_to_tree seq_pruf_verts' set_remove1_eq 2(4) by metis
  have V_V': "?V verts (a # seq) = insert b (?V (remove1 b verts) seq)"
    using contxt.verts_of_edges_prufer_to_tree 2 V' b_in_verts by blast
  have edges: "?E verts (a # seq) = insert {a,b} (?E (remove1 b verts) seq)"
    unfolding edges_of_edge_list_def using b_find by simp
  have b_notin_V': "b \<notin> ?V (remove1 b verts) seq" using V' by blast
  have a_in_V': "a \<in> ?V (remove1 b verts) seq"
    using V' b_notin_seq 2(2) unfolding prufer_sequences_def n_sequences_def by auto

  show ?case using V_V' edges tree'.add_vertex_tree[OF b_notin_V' a_in_V'] insert_commute by metis
qed (auto simp: prufer_sequences_def n_sequences_def)

lemma prufer_seq_to_tree_tree: "seq \<in> prufer_sequences verts \<Longrightarrow> (V,E) = prufer_seq_to_tree verts seq \<Longrightarrow> tree V E"
  unfolding prufer_seq_to_tree_def using prufer_seq_to_tree_edges_tree verts_of_edges_prufer_to_tree by auto

lemma labeled_tree_enum_tree: "(V,E) \<in> set (labeled_tree_enum verts) \<Longrightarrow> tree V E"
  using prufer_seq_to_tree_tree n_sequence_enum_correct unfolding labeled_tree_enum_def prufer_sequences_def by fastforce


lemma prufer_seq_to_tree_edges_wf:
  assumes pruf_seq: "seq \<in> prufer_sequences verts"
    and edge: "e \<in> edges_of_edge_list (prufer_seq_to_tree_edges verts seq)"
  shows "e \<subseteq> set verts"
  using prufer_seq_to_tree_context_axioms assms
proof (induction seq arbitrary: verts)
  case Nil
  then interpret prufer_seq_to_tree_context verts by simp
  obtain u v where "verts = [u,v]" using Nil verts_length unfolding prufer_sequences_def n_sequences_def apply auto
    by (metis (no_types, opaque_lifting) One_nat_def Suc_1 length_0_conv length_Suc_conv)
  then show ?case using Nil unfolding edges_of_edge_list_def by simp
next
  case (Cons a seq)
  then interpret prufer_seq_to_tree_context verts by simp
  obtain leaf where find_leaf: "find (\<lambda>v. v \<notin> set (a#seq)) verts = Some leaf"
    and pruf_seq': "seq \<in> prufer_sequences (remove1 leaf verts)"
    and leaf_in_verts: "leaf \<in> set verts"
    and "length (remove1 leaf verts) \<ge> 2"
    and "distinct (remove1 leaf verts)" using Cons obtain_b_prufer_seq_to_tree_edges by blast
  then have contxt': "prufer_seq_to_tree_context (remove1 leaf verts)" by (unfold_locales, simp)
  have a_in_verts: "a \<in> set verts" using Cons(3) unfolding prufer_sequences_def n_sequences_def by simp
  show ?case using Cons(4) Cons.IH[OF contxt' pruf_seq'] find_leaf a_in_verts leaf_in_verts
    unfolding edges_of_edge_list_def by (auto, (meson in_mk_uedge_img_iff notin_set_remove1)+)
qed

lemma distinct_prufer_seq_to_tree: "seq \<in> prufer_sequences verts \<Longrightarrow> distinct (map mk_edge (prufer_seq_to_tree_edges verts seq))"
  using prufer_seq_to_tree_context_axioms
proof (induction seq arbitrary: verts)
  case Nil
  then interpret prufer_seq_to_tree_context verts by simp
  obtain u v where "verts = [u,v]" using Nil verts_length unfolding prufer_sequences_def n_sequences_def apply auto
    by (metis (no_types, opaque_lifting) One_nat_def Suc_1 length_0_conv length_Suc_conv)
  then show ?case by auto
next
  case (Cons a seq)
  then interpret prufer_seq_to_tree_context verts by simp
  obtain leaf where find_leaf: "find (\<lambda>v. v \<notin> set (a#seq)) verts = Some leaf"
    and pruf_seq': "seq \<in> prufer_sequences (remove1 leaf verts)"
    and "length (remove1 leaf verts) \<ge> 2"
    and "distinct (remove1 leaf verts)" using Cons obtain_b_prufer_seq_to_tree_edges by blast
  then interpret contxt': prufer_seq_to_tree_context "remove1 leaf verts" by (unfold_locales, simp)
  have "leaf \<notin> set (remove1 leaf verts)" using distinct_verts set_remove1_eq by simp
  then have "{a, leaf} \<notin> edges_of_edge_list (prufer_seq_to_tree_edges (remove1 leaf verts) seq)"
    using contxt'.prufer_seq_to_tree_edges_wf pruf_seq' by blast
  then show ?case using find_leaf Cons pruf_seq' contxt'.prufer_seq_to_tree_context_axioms
    unfolding edges_of_edge_list_def by simp
qed

end

locale tree_to_prufer_seq_context =
  fixes verts :: "'a list"
    and edge_list :: "('a \<times> 'a) list"
  assumes distinct_verts: "distinct verts"
    and card_V: "card (set verts) \<ge> 2"
    and tree: "tree (set verts) (edges_of_edge_list edge_list)"
    and distinct_edges: "distinct (map mk_edge edge_list)"
begin

sublocale t: tree "set verts" "edges_of_edge_list edge_list" using tree .

lemma non_trivial: "t.non_trivial"
  using card_V unfolding t.non_trivial_def .

lemma length_verts: "length verts \<ge> 2"
  using card_V distinct_verts distinct_card by fastforce

sublocale prufer_seq_to_tree_context verts using length_verts distinct_verts prufer_seq_to_tree_context.intro by blast

lemma edge_ne: "(u,v) \<in> set edge_list \<Longrightarrow> u \<noteq> v"
  using t.two_edges tree unfolding edges_of_edge_list_def by fastforce

lemma distinct_edge_list: "distinct edge_list"
  using distinct_edges by (simp add: distinct_map)

lemma length_varts_edge_list: "length verts = Suc (length edge_list)"
  using distinct_verts t.card_V_card_E distinct_card distinct_edges edges_of_edge_list_def length_map list.set_map by metis

lemma incident_edges_correct: "edges_of_edge_list (incident_edges v edge_list) = t.incident_edges v"
  unfolding t.incident_edges_def t.incident_def by (auto simp: edges_of_edge_list_def incident_edges_def)

lemma degree_correct: "degree v edge_list = t.degree v"
proof-
  have distinct_incident_edges: "distinct (map mk_edge (incident_edges v edge_list))" unfolding incident_edges_def using distinct_map_filter distinct_edges by blast
  have "degree v edge_list = length (map mk_edge (incident_edges v edge_list))" using distinct_edges by simp
  also have "\<dots> = card (edges_of_edge_list (incident_edges v edge_list))" unfolding edges_of_edge_list_def using distinct_incident_edges distinct_card by fastforce
  also have "\<dots> = card (t.incident_edges v)" using incident_edges_correct by simp
  finally show ?thesis by simp
qed

lemma obtain_leaf_tree_to_prufer_seq:
  assumes length_edge_list: "length edge_list \<ge> 2"
  obtains leaf
  where "find (\<lambda>v. degree v edge_list = 1) verts = Some leaf"
    and "t.leaf leaf"
    and "leaf \<in> set verts"
    and "tree_to_prufer_seq_context (remove1 leaf verts) (remove_vertex leaf edge_list)"
proof-
  obtain leaf where leaf_find: "find (\<lambda>v. degree v edge_list = 1) verts = Some leaf"
    using find_None_iff2 t.leaf_in_V degree_correct t.leaf_def t.exists_leaf non_trivial by fastforce
  then have "degree leaf edge_list = 1"
    by (metis (mono_tags, lifting) find_Some_iff)
  then have leaf: "t.leaf leaf" using degree_correct t.leaf_def by auto
  have in_verts: "leaf \<in> set verts" by (simp add: leaf t.leaf_in_V)
  let ?verts' = "remove1 leaf verts"
  let ?edge_list' = "remove_vertex leaf edge_list"
  have distinct_verts': "distinct ?verts'" using distinct_verts distinct_remove1 by auto
  have "card (edges_of_edge_list edge_list) \<ge> 2" unfolding edges_of_edge_list_def using length_edge_list distinct_edges distinct_card by fastforce
  then have "card (set verts) \<ge> 3" using t.card_V_card_E by simp
  then have card_verts': "card (set ?verts') \<ge> 2" by (simp add: distinct_verts in_verts)
  then interpret t': tree "set ?verts'" "edges_of_edge_list ?edge_list'"
    using t.tree_remove_leaf leaf tree distinct_verts by (auto simp: remove_vertex t.remove_vertex_def t.incident_def)
  have distinct_edges': "distinct (map mk_edge ?edge_list')" using distinct_edges distinct_remove_vertex by simp
  then have "tree_to_prufer_seq_context ?verts' ?edge_list'" using distinct_verts' card_verts' by (unfold_locales, auto)
  then show ?thesis using that leaf_find leaf in_verts by auto
qed

lemma length_edge_list: "length edge_list \<ge> 1"
proof-
  have "length edge_list = card (edges_of_edge_list edge_list)" unfolding edges_of_edge_list_def using distinct_edges distinct_card by force
  then show ?thesis using t.card_V_card_E length_verts distinct_verts distinct_card by fastforce
qed

lemma pruf_seq_tree_to_prufer_seq: "tree_to_prufer_seq verts edge_list \<in> prufer_sequences verts"
  using tree_to_prufer_seq_context_axioms
proof (induction verts edge_list rule: tree_to_prufer_seq.induct)
  case (1 verts)
  then interpret contxt: tree_to_prufer_seq_context verts "[]"
    using tree_to_prufer_seq_context.intro by blast
  show ?case using contxt.length_edge_list by auto
next
  case (2 verts u w)
  then interpret contxt: tree_to_prufer_seq_context verts "[(u,w)]"
    using tree_to_prufer_seq_context.intro by blast
  show ?case using contxt.length_varts_edge_list unfolding prufer_sequences_def n_sequences_def by auto
next
  case (3 verts e1 e2 edges)
  let ?edge_list = "e1#e2#edges"
  interpret contxt: tree_to_prufer_seq_context verts ?edge_list
    using tree_to_prufer_seq_context.intro 3 by blast
  have length_edge_list: "length ?edge_list \<ge> 2" by simp
  then obtain leaf
    where find_leaf: "find (\<lambda>v. degree v ?edge_list = 1) verts = Some leaf"
      and contxt': "tree_to_prufer_seq_context (remove1 leaf verts) (remove_vertex leaf ?edge_list)"
    using contxt.obtain_leaf_tree_to_prufer_seq 3 by blast
  then interpret contxt': tree_to_prufer_seq_context "remove1 leaf verts" "remove_vertex leaf ?edge_list" by simp

  let ?neigh = "neighbor leaf ?edge_list"
  have degree: "degree leaf ?edge_list \<ge> 1" using find_Some find_leaf by fastforce
  have "?neigh \<in> set verts" using neighbor_edge_in_edges[OF degree] contxt.t.wellformed_alt_fst by blast
  then show ?case using find_leaf "3.IH" contxt' unfolding prufer_sequences_def n_sequences_def
    apply auto
    apply (meson notin_set_remove1 subset_code(1))
    by (metis Suc_diff_le Suc_length_remove1 contxt'.verts_length contxt.obtain_leaf_tree_to_prufer_seq find_leaf length_edge_list option.simps(1))
qed

lemma prufer_seq_in_verts: "v \<in> set (tree_to_prufer_seq verts edge_list) \<Longrightarrow> v \<in> set verts"
  using pruf_seq_tree_to_prufer_seq unfolding prufer_sequences_def n_sequences_def by auto

lemma degree_remove_vertex_non_adjacent:
  assumes "v \<noteq> u"
    and non_adjacent: "{v,u} \<notin> edges_of_edge_list edge_list"
  shows "degree u (remove_vertex v edge_list) = degree u edge_list"
proof -
  have "(v,u) \<notin> set edge_list \<and> (u,v) \<notin> set edge_list" using non_adjacent unfolding edges_of_edge_list_def by force
  then have "set (incident_edges u (remove_vertex v edge_list)) = set (incident_edges u edge_list)" unfolding incident_edges_def edges_of_edge_list_def remove_vertex_def using filter_filter \<open>v \<noteq> u\<close> by auto
  then show ?thesis using distinct_edges distinct_remove_vertex distinct_card distinct_filter distinct_map incident_edges_def by metis
qed

lemma count_list_pruf_seq_degree:
  assumes v_in_verts: "v \<in> set verts"
  shows "Suc (count_list (tree_to_prufer_seq verts edge_list) v) = degree v edge_list"
  using v_in_verts tree_to_prufer_seq_context_axioms
proof (induction verts edge_list rule: tree_to_prufer_seq.induct)
  case (1 verts)
  then interpret contxt: tree_to_prufer_seq_context verts "[]" using tree_to_prufer_seq_context.intro by blast
  show ?case using contxt.length_edge_list by auto
next
  case (2 verts u w)
  then interpret contxt: tree_to_prufer_seq_context verts "[(u,w)]" by simp
  interpret tr: tree "set verts" "{{u,w}}" using contxt.tree unfolding edges_of_edge_list_def by simp
  have "set verts = {u,w}" using tr.V_Union_E contxt.non_trivial by blast
  then show ?case unfolding incident_edges_def using 2 by auto
next
  case (3 verts e1 e2 edges)
  let ?edge_list = "e1#e2#edges"
  interpret contxt: tree_to_prufer_seq_context verts ?edge_list using tree_to_prufer_seq_context.intro 3 by blast
  have "length ?edge_list \<ge> 2" by simp
  then obtain leaf
    where find_leaf: "find (\<lambda>v. degree v ?edge_list = 1) verts = Some leaf"
      and leaf: "contxt.t.leaf leaf"
      and leaf_in_verts: "leaf \<in> set verts"
      and contxt': "tree_to_prufer_seq_context (remove1 leaf verts) (remove_vertex leaf ?edge_list)"
    using contxt.obtain_leaf_tree_to_prufer_seq 3 by blast
  then interpret contxt': tree_to_prufer_seq_context "remove1 leaf verts" "remove_vertex leaf ?edge_list" using tree_to_prufer_seq_context.intro by blast
  let ?neigh = "neighbor leaf ?edge_list"
  have degree_leaf: "degree leaf ?edge_list = 1" using find_leaf find_Some by fast
  show ?case
  proof (cases "v = leaf")
    case True
    have "leaf \<notin> set (remove1 leaf verts)" using contxt.distinct_verts set_remove1_eq by auto
    then have leaf_notin_pruf_seq': "leaf \<notin> set (tree_to_prufer_seq (remove1 leaf verts) (remove_vertex leaf (e1 # e2 # edges)))"
      using contxt'.prufer_seq_in_verts True by blast

    have "neighbor leaf ?edge_list \<noteq> leaf"
      using degree_leaf by (simp add: contxt.t.edge_vertices_not_equal neighbor_edge_in_edges)
    then show ?thesis using find_leaf True leaf_notin_pruf_seq' degree_leaf by auto
  next
    case False
    then have "v \<in> set (remove1 leaf verts)" using 3 set_remove1_eq by auto
    then have IH: "Suc (count_list (tree_to_prufer_seq (remove1 leaf verts) (remove_vertex leaf ?edge_list)) v)
      = degree v (remove_vertex leaf ?edge_list)" using "3.IH" find_leaf contxt' by blast
    then show ?thesis
    proof (cases "v = ?neigh")
      case True
      then show ?thesis using degree_neighbor_remove_vertex[OF degree_leaf] find_leaf IH by auto
    next
      case False
      have "{leaf, v} \<notin> edges_of_edge_list ?edge_list"
      proof
        assume "{leaf, v} \<in> edges_of_edge_list ?edge_list"
        then have leaf_v_edge: "{leaf, v} \<in> edges_of_edge_list (incident_edges leaf ?edge_list)"
          unfolding contxt.incident_edges_correct contxt.t.incident_edges_def contxt.t.incident_def by simp
        have "{?neigh, leaf} \<in> edges_of_edge_list ?edge_list" using neighbor_edge_in_edges degree_leaf degree_length_filter by force
        then have "{?neigh, leaf} \<in> edges_of_edge_list (incident_edges leaf ?edge_list)"
          unfolding contxt.incident_edges_correct contxt.t.incident_edges_def contxt.t.incident_def by simp
        then show False using leaf_v_edge degree_leaf
          by (metis False One_nat_def card_le_Suc0_iff_eq contxt.degree_correct contxt.incident_edges_correct
              contxt.t.alt_degree_def contxt.t.fin_edges contxt.t.finite_incident_edges insert_iff le_numeral_extra(4) singletonD)
      qed
      then show ?thesis using False find_leaf IH find_leaf  \<open>v \<noteq> leaf\<close> contxt.degree_remove_vertex_non_adjacent by auto
    qed
  qed
qed

lemma notin_set_tree_to_prufer_seq:
  assumes v_in_verts: "v \<in> set verts"
  shows "v \<notin> set (tree_to_prufer_seq verts edge_list) \<longleftrightarrow> degree v edge_list = 1"
  using count_list_pruf_seq_degree assms count_list_zero_not_elem by force

lemma find_Some_impl_eq: "find P xs = Some x \<Longrightarrow> \<forall>x. Q x \<longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> find Q xs = Some x"
  by (induction xs) (auto split: if_splits) 


lemma pruf_seq_to_tree_to_pruf_seq: "edges_of_edge_list (prufer_seq_to_tree_edges verts (tree_to_prufer_seq verts edge_list)) = edges_of_edge_list edge_list"
  using tree_to_prufer_seq_context_axioms
proof (induction verts edge_list rule: tree_to_prufer_seq.induct)
  case (1 verts)
  then interpret contxt: tree_to_prufer_seq_context verts "[]" using tree_to_prufer_seq_context.intro by blast
  show ?case using contxt.length_edge_list by auto
next
  case (2 verts u w)
  then interpret contxt: tree_to_prufer_seq_context verts "[(u, w)]" by simp
  interpret tr: tree "set verts" "{{u,w}}" using contxt.tree unfolding edges_of_edge_list_def by simp
  have card_verts: "card (set verts) = 2" using tr.card_V_card_E by force
  then have set_verts: "set verts = {u,w}" using tr.V_Union_E contxt.non_trivial by simp
  have "length verts = Suc (Suc 0)" using contxt.distinct_verts card_verts distinct_card by fastforce
  then have "\<exists>a b. verts = [a,b]" by (metis length_0_conv length_Suc_conv)
  then show ?case unfolding edges_of_edge_list_def using set_verts by force
next
  case (3 verts e1 e2 es)
  let ?edge_list = "e1#e2#es"
  interpret contxt: tree_to_prufer_seq_context verts ?edge_list using 3 tree_to_prufer_seq_context.intro by blast
  have "length ?edge_list \<ge> 2" by simp
  then obtain leaf
    where find_leaf: "find (\<lambda>v. degree v ?edge_list = 1) verts = Some leaf"
    and leaf: "contxt.t.leaf leaf"
    and leaf_in_verts: "leaf \<in> set verts"
    and contxt': "tree_to_prufer_seq_context (remove1 leaf verts) (remove_vertex leaf ?edge_list)"
    using contxt.obtain_leaf_tree_to_prufer_seq 3 by blast
  then interpret contxt': tree_to_prufer_seq_context "remove1 leaf verts" "remove_vertex leaf ?edge_list" by simp

  have degree_leaf: "degree leaf ?edge_list = 1" using find_leaf find_Some by fast
  have find_not_in_seq: "find (\<lambda>v. v \<notin> set (tree_to_prufer_seq verts ?edge_list)) verts = Some leaf"
    using find_leaf contxt.notin_set_tree_to_prufer_seq find_cong by force
  show ?case using find_not_in_seq find_leaf "3.IH" find_leaf contxt' insert_remove_leaf[OF degree_leaf]
    unfolding edges_of_edge_list_def by simp
qed

end

context prufer_seq_to_tree_context
begin

lemma tree_labeled_tree_enum:
  assumes t: "tree (set verts) E"
  shows "(set verts, E) \<in> set (labeled_tree_enum verts)"
proof-
  interpret t: tree "set verts" E using t .
  obtain edges where set_edges: "set edges = E" and  distinct_edges: "distinct edges" using finite_distinct_list t.fin_edges by blast
  let ?edge_list = "map (\<lambda>e. SOME uv. mk_edge uv = e) edges"
  have "\<forall>e\<in>E. \<exists>uv. mk_edge uv = e" using t.two_edges card_2_iff by (metis mk_edge.simps)
  then have "\<And>e. e \<in> E \<Longrightarrow> (mk_edge o (\<lambda>e. SOME uv. mk_edge uv = e)) e = e" using someI_ex
    by (smt (verit, del_insts) comp_apply)
  then have map_edges: "map mk_edge ?edge_list = edges" unfolding map_map using map_idI set_edges by blast
  then have edge_list: "edges_of_edge_list ?edge_list = E" unfolding edges_of_edge_list_def using set_edges set_map by metis
  have distinct_edge_list: "distinct (map mk_edge ?edge_list)" using distinct_edges map_edges by metis
  
  then interpret contxt: tree_to_prufer_seq_context verts ?edge_list using t tree_to_prufer_seq_context.intro distinct_verts edge_list card_verts by blast
  show ?thesis
    using contxt.pruf_seq_tree_to_prufer_seq contxt.pruf_seq_to_tree_to_pruf_seq n_sequence_enum_correct distinct_edge_list edge_list
    unfolding prufer_sequences_def prufer_seq_to_tree_def labeled_tree_enum_def by auto
qed

lemma V_labeled_tree_enum_verts: "(V,E) \<in> set (labeled_tree_enum verts) \<Longrightarrow> V = set verts"
  unfolding labeled_tree_enum_def by (metis Pair_inject ex_map_conv prufer_seq_to_tree_def)

theorem labeled_tree_enum_correct: "set (labeled_tree_enum verts) = labeled_trees (set verts)"
  using labeled_tree_enum_tree V_labeled_tree_enum_verts tree_labeled_tree_enum unfolding labeled_trees_def by auto


subsection \<open>Distinctness\<close>

lemma count_list_degree: "seq \<in> prufer_sequences verts \<Longrightarrow> v \<in> set verts \<Longrightarrow> Suc (count_list seq v) = degree v (prufer_seq_to_tree_edges verts seq)"
  using verts_length distinct_verts
proof (induction verts seq rule: prufer_seq_to_tree_edges.induct)
  case (1 u w)
  then show ?case unfolding incident_edges_def by auto
next
  case (2 verts a seq)
  then interpret contxt: prufer_seq_to_tree_context verts by unfold_locales
  obtain leaf
    where leaf_find: "find (\<lambda>x. x \<notin> set (a # seq)) verts = Some leaf"
      and leaf_not_in_seq: "leaf \<notin> set (a#seq)"
      and seq_in_verts': "seq \<in> prufer_sequences (remove1 leaf verts)"
      and len_verts': "2 \<le> length (remove1 leaf verts)"
      and distinct_verts': "distinct (remove1 leaf verts)"
      and leaf_in_verts: "leaf \<in> set verts" using contxt.obtain_b_prufer_seq_to_tree_edges 2 by blast
  interpret contxt': prufer_seq_to_tree_context "remove1 leaf verts" using len_verts' distinct_verts' by unfold_locales
  show ?case
  proof (cases "v = leaf")
    case True
    then have "a \<noteq> leaf" using 2 leaf_not_in_seq by auto
    interpret t: tree "set (remove1 leaf verts)" "edges_of_edge_list (prufer_seq_to_tree_edges (remove1 leaf verts) seq)"
      using contxt'.prufer_seq_to_tree_edges_tree seq_in_verts' by auto
    have [simp]: "set (remove1 leaf verts) = set verts - {leaf}" using set_remove1_eq 2 by auto
    then have "\<forall>(u,w)\<in>set (prufer_seq_to_tree_edges (remove1 leaf verts) seq). u \<noteq> leaf \<and> w \<noteq> leaf"
      using t.wellformed in_mk_edge_img unfolding edges_of_edge_list_def apply auto by fast+
    then have "degree v (prufer_seq_to_tree_edges (remove1 leaf verts) seq) = 0"
      unfolding incident_edges_def filter_False True by (auto split: prod.splits)
    then show ?thesis using \<open>a\<noteq>leaf\<close> True leaf_find leaf_not_in_seq unfolding incident_edges_def by simp
  next
    case False
    then show ?thesis using 2 leaf_find seq_in_verts' len_verts' unfolding incident_edges_def by auto
  qed
qed (auto simp: prufer_sequences_def n_sequences_def)

lemma vert_notin_pruf_seq_leaf: "seq \<in> prufer_sequences verts \<Longrightarrow> v \<in> set verts \<Longrightarrow> v \<notin> set seq \<longleftrightarrow> degree v (prufer_seq_to_tree_edges verts seq) = 1"
  using count_list_degree count_list_zero_not_elem by fastforce

lemma inj_prufer_seq_to_tree_edges:
  assumes pruf_seq1: "seq1 \<in> prufer_sequences verts"
    and pruf_seq2: "seq2 \<in> prufer_sequences verts"
    and seq_ne: "seq1 \<noteq> seq2"
  shows "edges_of_edge_list (prufer_seq_to_tree_edges verts seq1) \<noteq> edges_of_edge_list (prufer_seq_to_tree_edges verts seq2)" (is "?l \<noteq> ?r")
proof
  assume trees_eq: "?l = ?r"
  have "length seq1 = length seq2" using pruf_seq1 pruf_seq2 unfolding prufer_sequences_def n_sequences_def by simp
  then show False
    using assms \<open>?l = ?r\<close> prufer_seq_to_tree_context_axioms
  proof (induction seq1 seq2 arbitrary: verts rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    then interpret prufer_seq_to_tree_context verts by simp
    interpret t1: tree "set verts" "edges_of_edge_list (prufer_seq_to_tree_edges verts (x#xs))" using Cons(3) prufer_seq_to_tree_edges_tree by fastforce
    interpret t2: tree "set verts" "edges_of_edge_list (prufer_seq_to_tree_edges verts (y#ys))" using Cons(4) prufer_seq_to_tree_edges_tree by fastforce
    obtain leaf where find_leaf: "find (\<lambda>v. v \<notin> set (x#xs)) verts = Some leaf"
      and pruf_seq1': "xs \<in> prufer_sequences (remove1 leaf verts)"
      and "length (remove1 leaf verts) \<ge> 2"
      and "distinct (remove1 leaf verts)" using obtain_b_prufer_seq_to_tree_edges Cons(3) by blast
    then interpret contxt': prufer_seq_to_tree_context "remove1 leaf verts" by (unfold_locales, simp)
    obtain leaf2 where find_leaf2: "find (\<lambda>v. v \<notin> set (y#ys)) verts = Some leaf2"
      and pruf_seq2': "ys \<in> prufer_sequences (remove1 leaf2 verts)" using obtain_b_prufer_seq_to_tree_edges Cons(4) by blast
    interpret ttps_contxt1: tree_to_prufer_seq_context verts "prufer_seq_to_tree_edges verts (x#xs)"
      using distinct_verts verts_length distinct_prufer_seq_to_tree[OF Cons(3)] by (unfold_locales, auto simp: distinct_card)
    interpret ttps_contxt2: tree_to_prufer_seq_context verts "prufer_seq_to_tree_edges verts (y#ys)"
      using distinct_verts verts_length distinct_prufer_seq_to_tree[OF Cons(4)] by (unfold_locales, auto simp: distinct_card)
    have 1: "find (\<lambda>v. v \<notin> set (x#xs)) verts = find (\<lambda>v. t1.leaf v) verts" using vert_notin_pruf_seq_leaf[OF Cons(3)] ttps_contxt1.degree_correct find_cong unfolding t1.leaf_def by force
    have 2: "find (\<lambda>v. v \<notin> set (y#ys)) verts = find (\<lambda>v. t2.leaf v) verts" using vert_notin_pruf_seq_leaf[OF Cons(4)] ttps_contxt2.degree_correct find_cong unfolding t2.leaf_def by force
    have "find (\<lambda>v. v \<notin> set (x#xs)) verts = find (\<lambda>v. v \<notin> set (y#ys)) verts" using Cons(6) 1 2 unfolding t1.leaf_def t2.leaf_def by simp
    have leafs_eq: "leaf2 = leaf" using Cons(6) 1 2 find_leaf find_leaf2 unfolding t1.leaf_def t2.leaf_def by simp
    have leaf_not_in_verts': "leaf \<notin> set (remove1 leaf verts)" using distinct_verts set_remove1_eq by simp
    show False
    proof (cases "y = x")
      case True
      then have "xs \<noteq> ys" using Cons by simp
      have 1: "{x, leaf} \<notin> edges_of_edge_list (prufer_seq_to_tree_edges (remove1 leaf verts) xs)" using contxt'.prufer_seq_to_tree_edges_wf pruf_seq1' leaf_not_in_verts' by blast
      have 2: "{x, leaf} \<notin> edges_of_edge_list (prufer_seq_to_tree_edges (remove1 leaf verts) ys)" using contxt'.prufer_seq_to_tree_edges_wf pruf_seq2' leaf_not_in_verts' True leafs_eq by blast
      then have "edges_of_edge_list (prufer_seq_to_tree_edges (remove1 leaf verts) xs) = edges_of_edge_list (prufer_seq_to_tree_edges (remove1 leaf verts) ys)"
        using Cons(6) find_leaf find_leaf2 leafs_eq True insert_ident[OF 1 2] unfolding edges_of_edge_list_def by simp
      then show ?thesis using True leafs_eq Cons.IH pruf_seq1' pruf_seq2' leafs_eq Cons(6) find_leaf
          find_leaf2 \<open>xs \<noteq> ys\<close> contxt'.prufer_seq_to_tree_context_axioms unfolding edges_of_edge_list_def by auto
    next
      case False
      then have "{x, leaf} \<notin> edges_of_edge_list (prufer_seq_to_tree_edges (remove1 leaf verts) ys)" using find_leaf2 leafs_eq contxt'.prufer_seq_to_tree_edges_wf pruf_seq2' leaf_not_in_verts' by auto
      then show ?thesis using Cons(6) find_leaf find_leaf2 leafs_eq False unfolding edges_of_edge_list_def
        by (auto, metis (no_types, lifting) doubleton_eq_iff insert_iff)
    qed
  qed
qed

lemma inj_on_prufer_seq_to_tree: "inj_on (prufer_seq_to_tree verts) (prufer_sequences verts)"
  unfolding inj_on_def prufer_seq_to_tree_def using inj_prufer_seq_to_tree_edges by auto

theorem labeled_tree_enum_distinct: "distinct (labeled_tree_enum verts)"
  unfolding labeled_tree_enum_def using inj_on_prufer_seq_to_tree
  by (simp add: distinct_map n_sequence_enum_correct n_sequence_enum_distinct prufer_sequences_def distinct_verts)


end

end