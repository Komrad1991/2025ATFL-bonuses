require 'ruby-graphviz'
require 'set'

class Bonuses
  def correct?(graph)
    transitions = Hash.new { |h, k| h[k] = {} }
    alphabet = Set.new
    states = Set.new

    graph.each_edge do |edge|
      from = edge.node_one.to_s
      to   = edge.node_two.to_s
      label = edge[:label].to_s.delete_prefix('"').delete_suffix('"').strip

      states << from
      states << to
      return false if label == 'ε'
      next if label.empty?

      symbols = label.split(',').map(&:strip)
      symbols.each do |sym|
        return false if transitions[from].key?(sym)
        transitions[from][sym] = to
        alphabet << sym
      end
    end

    has_initial = graph.each_node.any? { |_, n| n[:style].to_s.include?('bold') }
    return false unless has_initial

    states.each do |state|
      alphabet.each { |sym| return false unless transitions[state]&.key?(sym) }
    end

    true
  rescue
    false
  end

  def minimize(dotfile_name)
    base_name = File.basename(dotfile_name, ".dot")

    graph = GraphViz.parse(dotfile_name)
    graph.output(png: "#{base_name}_original.png")

    return false unless correct?(graph)

    transitions = {}
    alphabet = Set.new
    states = []
    accepting = Set.new

    graph.each_node do |name, node|
      states << name.to_s
      accepting << name.to_s if node[:shape].to_s.include?('doublecircle')
    end

    graph.each_edge do |edge|
      from = edge.node_one.to_s
      to   = edge.node_two.to_s
      label = edge[:label].to_s.delete_prefix('"').delete_suffix('"').strip
      next if label.empty?
      symbols = label.split(',').map(&:strip)
      transitions[from] ||= {}
      symbols.each do |sym|
        transitions[from][sym] = to
        alphabet << sym
      end
    end

    p_sets = [accepting, states.to_set - accepting].reject(&:empty?)
    w = p_sets.dup

    until w.empty?
      a = w.pop
      alphabet.each do |c|
        x = states.select { |s| transitions[s] && a.include?(transitions[s][c]) }
        p_sets.dup.each do |y|
          intersection = y & x
          difference   = y - x
          next if intersection.empty? || difference.empty?

          p_sets.delete(y)
          p_sets << intersection
          p_sets << difference

          if w.include?(y)
            w.delete(y)
            w << intersection
            w << difference
          else
            w << (intersection.size <= difference.size ? intersection : difference)
          end
        end
      end
    end

    state_mapping = {}
    p_sets.each do |cls|
      name = "q#{state_mapping.size}"
      state_mapping[cls] = name
    end

    min_graph = GraphViz.new(:G, type: :digraph, rankdir: 'LR', ranksep: 1.0, nodesep: 0.6)

    p_sets.each do |cls|
      name = state_mapping[cls]
      node_shape = cls.any? { |s| accepting.include?(s) } ? 'doublecircle' : 'circle'
      node_style = cls.any? { |s| s == 'q0' } ? 'bold' : ''
      min_graph.add_nodes(name, shape: node_shape, style: node_style, fontsize: 14)
    end

    added_edges = Set.new
    transitions.each do |from, trans|
      from_cls = p_sets.find { |cls| cls.include?(from) }
      from_name = state_mapping[from_cls]
      trans.each do |sym, to|
        to_cls = p_sets.find { |cls| cls.include?(to) }
        to_name = state_mapping[to_cls]
        edge_key = [from_name, to_name, sym]
        next if added_edges.include?(edge_key)
        min_graph.add_edges(from_name, to_name, label: sym, fontsize: 12)
        added_edges << edge_key
      end
    end

    min_graph.output(png: "#{base_name}_minimized.png")
    min_graph.output(dot: "#{base_name}_minimized.dot")

    "#{base_name}_minimized.png and .dot generated"
  rescue => e
    puts "Exception: #{e}"
    false
  end

  def petri?(dotfile)
    graph = GraphViz.parse(dotfile)

    node_type = {}
    graph.each_node do |name, node|
      shape = node[:shape].to_s.strip.delete_prefix('"').delete_suffix('"')
      return false unless ["circle", "box"].include?(shape)
      node_type[name.to_s] = shape
    end

    graph.each_edge do |edge|
      from = edge.node_one.to_s
      to   = edge.node_two.to_s

      shape_from = node_type[from]
      shape_to   = node_type[to]

      return false if shape_from == shape_to
    end

    true
  rescue => e
    false
  end

  def petri_cover(dotfile, initial_marking)
    base_name = File.basename(dotfile, ".dot")

    graph = GraphViz.parse(dotfile)
    graph.output(png: "#{base_name}_original.png")
    places = Set.new
    transitions = {}

    graph.each_node do |name, node|
      id = name.to_s
      shape = node[:shape].to_s.delete_prefix('"').delete_suffix('"').strip
      if shape == 'circle' || id.start_with?('p')
        places << id
      elsif shape == 'box' || id.start_with?('t')
        transitions[id] = { in: [], out: [] }
      end
    end

    graph.each_edge do |edge|
      from = edge.node_one.to_s
      to   = edge.node_two.to_s
      if places.include?(from) && transitions.key?(to)
        transitions[to][:in] << from
      elsif transitions.key?(from) && places.include?(to)
        transitions[from][:out] << to
      end
    end

    marking0 = {}
    places.each { |p| marking0[p] = (initial_marking[p] || 0) }

    place_list = places.to_a.sort

    serialize = ->(m) {
      place_list.map { |p| (m[p] == Float::INFINITY) ? 'inf' : (m[p] || 0).to_s }.join(',')
    }

    covers_strict = ->(new_m, anc_m) {
      nondecreasing = place_list.all? do |p|
        anc_v = anc_m[p]
        new_v = new_m[p]
        if anc_v == Float::INFINITY
          new_v == Float::INFINITY
        else
          new_v == Float::INFINITY || ((new_v || 0) >= (anc_v || 0))
        end
      end
      return false unless nondecreasing

      place_list.any? do |p|
        anc_v = anc_m[p]
        new_v = new_m[p]
        next false if anc_v == Float::INFINITY
        (new_v == Float::INFINITY) || ((new_v || 0) > (anc_v || 0))
      end
    }

    apply_inf = ->(new_m, anc_m) {
      nm = {}
      place_list.each do |p|
        anc_v = anc_m[p]
        new_v = new_m[p]
        if anc_v != Float::INFINITY && new_v != Float::INFINITY && (new_v || 0) > (anc_v || 0)
          nm[p] = Float::INFINITY
        elsif anc_v != Float::INFINITY && new_v == Float::INFINITY
          nm[p] = Float::INFINITY
        else
          nm[p] = new_v
        end
      end
      nm
    }

    base_name = File.basename(dotfile, ".dot")
    tree = GraphViz.new(:G, type: :digraph, rankdir: 'TB', nodesep: 0.6, ranksep: 0.8)

    node_id_counter = 0
    visited_keys = Set.new

    stack = []
    stack << { m: marking0, parent: nil, ancestors: [] }

    while !stack.empty?
      cur = stack.pop
      m = cur[:m]
      parent = cur[:parent]
      ancestors = cur[:ancestors]

      key = serialize.call(m)
      next if visited_keys.include?(key)

      visited_keys << key

      nid = "n#{node_id_counter}"; node_id_counter += 1
      label = place_list.map { |p| "#{p}=#{m[p] == Float::INFINITY ? '∞' : m[p]}" }.join("\\n")
      tree.add_nodes(nid, label: label, shape: 'ellipse', fontsize: 10)
      tree.add_edges(parent, nid) if parent

      enabled_any = false

      transitions.each do |t, io|
        enabled = io[:in].all? { |p| m[p] == Float::INFINITY || (m[p] || 0) > 0 }
        next unless enabled

        enabled_any = true
        nm = {}
        place_list.each { |p| nm[p] = (m[p] == Float::INFINITY ? Float::INFINITY : (m[p] || 0)) }

        io[:in].each { |p| nm[p] -= 1 unless nm[p] == Float::INFINITY }
        io[:out].each { |p| nm[p] = nm[p] + 1 unless nm[p] == Float::INFINITY }

        ancestors.each do |anc|
          if covers_strict.call(nm, anc)
            nm = apply_inf.call(nm, anc)
            break
          end
        end

        nkey = serialize.call(nm)
        if visited_keys.include?(nkey)
          child_id = "n#{node_id_counter}"; node_id_counter += 1
          child_label = place_list.map { |p| "#{p}=#{nm[p] == Float::INFINITY ? '∞' : nm[p]}" }.join("\\n")
          tree.add_nodes(child_id, label: child_label, shape: 'box', fontsize: 10)
          tree.add_edges(nid, child_id)
          next
        end

        stack << { m: nm, parent: nid, ancestors: ancestors + [m] }
      end
    end

    dot_file = "#{base_name}_tree.dot"
    png_file = "#{base_name}_tree.png"
    tree.output(dot: dot_file)
    tree.output(png: png_file)

    { dot: dot_file, png: png_file }
  end

  def clear_grammar(input_file)
    dir = File.dirname(input_file)
    base = File.basename(input_file, ".*")
    ext = File.extname(input_file)
    output_file = File.join(dir, "#{base}_cleaned#{ext}")

    grammar = {}

    File.readlines(input_file).each do |line|
      line.strip!
      next if line.empty? || line.start_with?('#')

      if line.include?('->')
        left, right = line.split('->', 2)
        nonterm = left.strip
        productions = right.strip.split('|').map(&:strip)

        grammar[nonterm] ||= []
        grammar[nonterm].concat(productions)
      end
    end

    terminal = ->(ch) { ch.match?(/[a-z]|\d|\+|\-|\*|\/|\(|\)|:|,|;|\s/) }

    f = Set.new
    q = []

    is_all_in_f = ->(s) do
      s.chars.all? do |ch|
        terminal.call(ch) || f.include?(ch)
      end
    end

    grammar.each do |nonterm, productions|
      productions.each do |prod|
        if prod.chars.all? { |ch| terminal.call(ch) }
          f.add(nonterm)
          q << nonterm
          break
        end
      end
    end

    until q.empty?
      p = q.shift

      grammar.each do |nonterm, productions|
        next if f.include?(nonterm)

        productions.each do |prod|
          if is_all_in_f.call(prod)
            f.add(nonterm)
            q << nonterm
            break
          end
        end
      end
    end

    result1 = {}
    grammar.each do |nonterm, productions|
      if f.include?(nonterm)
        result1[nonterm] ||= []
        productions.each do |prod|
          valid = true
          prod.chars.each do |ch|
            if !terminal.call(ch) && !f.include?(ch)
              valid = false
              break
            end
          end
          result1[nonterm] << prod if valid
        end
      end
    end

    grammar = result1

    reachable = Set.new(['S'])
    q = ['S']

    until q.empty?
      a = q.shift
      (grammar[a] || []).each do |prod|
        prod.chars.each do |ch|
          if !terminal.call(ch) && !reachable.include?(ch)
            reachable.add(ch)
            q << ch
          end
        end
      end
    end

    result2 = {}
    reachable.each do |nonterm|
      next unless grammar.key?(nonterm)

      grammar[nonterm].each do |prod|
        valid = prod.chars.all? do |ch|
          terminal.call(ch) || reachable.include?(ch)
        end

        if valid
          result2[nonterm] ||= []
          result2[nonterm] << prod
        end
      end
    end

    grammar = result2

    File.open(output_file, 'w') do |file|
      grammar.sort.each do |nonterm, productions|
        unless productions.empty?
          file.puts("#{nonterm} -> #{productions.join(' | ')}")
        end
      end
    end

    output_file
  end
end

check = Bonuses.new
marking = {
  "p1" => 1,
  "p2" => 0,
  "p3" => 0,
  "p4" => 0,
}
check.petri_cover("petri1.dot", marking)
check.minimize('correct.dot')
check.clear_grammar("bad_grammar.txt")