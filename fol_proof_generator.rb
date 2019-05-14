# frozen_string_literal: true

# Requires
require 'nokogiri'
require 'open-uri'
require 'set'

# Constants
FILES = (1..15).map { |idx| "http://us.metamath.org/mpeuni/mmtheorems#{idx}.html" }
PROOFS_FOLDER = './proofs'
INITIAL = 'a'.ord
FINAL = 'z'.ord + 1

proofs = FILES.map do |file|
  puts "Processing file #{file}"
  Nokogiri::HTML(open(file)).css('tr td')
          .select { |td| td['colspan'].to_i == 3 }
          .map { |td| td.text.gsub(/[[:space:]]/, '') }
          .select do |td|
    td != '' && td.include?('⊢') &&
      !/[A-Z]|[[0-9]+\.[0-9]+\.[0-9]+]/.match?(td) && !/^.*(add|⊼|⊻|⊤).*$/.match?(td)
  end
end.flatten
puts "Parsed #{proofs.length} proofs"

# We create 4 differentes types os formulas:
#   * Variables in alphabetic ascending order
#   * Variables in alphabetic descending order
#   * Random variables (this should create some provable theorems, but most unprovable (in theory))
#   * Negation of the first part of the sequent (this should create theorems not provable)
puts 'Substituting variables'
proofs = proofs.map do |proof|
  [26.times.map do |index|
    inicial = INITIAL + index
    hashmap = {
      '𝜑': inicial.chr,
      '𝜓': (inicial + 1 < FINAL ? inicial + 1 : INITIAL + inicial + 1 - FINAL).chr,
      '𝜒': (inicial + 2 < FINAL ? inicial + 2 : INITIAL + inicial + 2 - FINAL).chr,
      '𝜃': (inicial + 3 < FINAL ? inicial + 3 : INITIAL + inicial + 3 - FINAL).chr,
      '𝜏': (inicial + 4 < FINAL ? inicial + 4 : INITIAL + inicial + 4 - FINAL).chr,
      '𝜂': (inicial + 5 < FINAL ? inicial + 5 : INITIAL + inicial + 5 - FINAL).chr,
      '𝜁': (inicial + 6 < FINAL ? inicial + 6 : INITIAL + inicial + 6 - FINAL).chr,
      '𝜎': (inicial + 7 < FINAL ? inicial + 7 : INITIAL + inicial + 7 - FINAL).chr,
      '𝜇': (inicial + 8 < FINAL ? inicial + 8 : INITIAL + inicial + 8 - FINAL).chr,
      '𝜆': (inicial + 9 < FINAL ? inicial + 9 : INITIAL + inicial + 9 - FINAL).chr,
      '𝜅': (inicial + 10 < FINAL ? inicial + 10 : INITIAL + inicial + 10 - FINAL).chr,
      '𝜌': (inicial + 11 < FINAL ? inicial + 11 : INITIAL + inicial + 11 - FINAL).chr,
      '⊢': '',
      '¬': '-',
      '⊥': 'F',
      '→': ' => ',
      '↔': ' <=> ',
      '&': ' & ',
      '∧': ' & ',
      '∨': ' + ',
      '⇒': ') => ('
    }
    regex = Regexp.new(hashmap.keys.join('|'))

    parsed_proof = '(' + proof.gsub(regex) { |variable| hashmap[variable.to_sym] } + ').'

    # Returns a normal, and a denied form, to create some false proofs
    [parsed_proof, "-#{parsed_proof}"]
  end.flatten,
   26.times.map do |index|
     final = FINAL - index - 1
     hashmap = {
       '𝜑': final.chr,
       '𝜓': (final - 1 > INITIAL ? final - 1 : FINAL + final - 1 - INITIAL).chr,
       '𝜒': (final - 2 > INITIAL ? final - 2 : FINAL + final - 2 - INITIAL).chr,
       '𝜃': (final - 3 > INITIAL ? final - 3 : FINAL + final - 3 - INITIAL).chr,
       '𝜏': (final - 4 > INITIAL ? final - 4 : FINAL + final - 4 - INITIAL).chr,
       '𝜂': (final - 5 > INITIAL ? final - 5 : FINAL + final - 5 - INITIAL).chr,
       '𝜁': (final - 6 > INITIAL ? final - 6 : FINAL + final - 6 - INITIAL).chr,
       '𝜎': (final - 7 > INITIAL ? final - 7 : FINAL + final - 7 - INITIAL).chr,
       '𝜇': (final - 8 > INITIAL ? final - 8 : FINAL + final - 8 - INITIAL).chr,
       '𝜆': (final - 9 > INITIAL ? final - 9 : FINAL + final - 9 - INITIAL).chr,
       '𝜅': (final - 10 > INITIAL ? final - 10 : FINAL + final - 10 - INITIAL).chr,
       '𝜌': (final - 11 > INITIAL ? final - 11 : FINAL + final - 11 - INITIAL).chr,
       '⊢': '',
       '¬': '-',
       '⊥': 'F',
       '→': ' => ',
       '↔': ' <=> ',
       '&': ' & ',
       '∧': ' & ',
       '∨': ' + ',
       '⇒': ') => ('
     }
     regex = Regexp.new(hashmap.keys.join('|'))

     '(' + proof.gsub(regex) { |variable| hashmap[variable.to_sym] } + ').'
   end,
   26.times.map do
     variables = Regexp.new(%w[𝜑 𝜓 𝜒 𝜃 𝜏 𝜂 𝜁 𝜎 𝜇 𝜆 𝜅 𝜌].join('|'))
     hashmap = {
       '⊢': '',
       '¬': '-',
       '⊥': 'F',
       '→': ' => ',
       '↔': ' <=> ',
       '&': ' & ',
       '∧': ' & ',
       '∨': ' + ',
       '⇒': ') => ('
     }
     regex = Regexp.new(hashmap.keys.join('|'))

     '(' + proof.gsub(variables) { |_variable| rand(INITIAL...FINAL).chr }
                .gsub(regex) { |variable| hashmap[variable.to_sym] } + ').'
   end]
end.flatten
puts 'Done with substituting variables'
puts "Generated #{proofs.length} proofs"

puts 'Start proving'
threads = proofs.each_with_index.map do |proof, index|
  Thread.new(proof, "#{PROOFS_FOLDER}/#{index}") do |pr, file_name|
    system "echo '#{pr}' > #{file_name}.proof" # Write formula to file
    system "timeout 5 ./base_prover -p '#{file_name}.proof' >> #{file_name}.proof" # Get the proof
  end
end

puts 'Joining threads...'
threads.each(&:join)
puts 'Done!'
