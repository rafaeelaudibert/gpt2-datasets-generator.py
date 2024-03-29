# frozen_string_literal: true

require 'matrix'
require 'rubystats'
require 'fileutils'
require 'optparse'

# Arg Parsing
options = {}
OptionParser.new do |opt|
  opt.on('-i', '--iterations ITERATIONS') { |o| options[:iterations] = o.to_i }
  opt.on('-d', '--matrix_dimension DIMENSION') { |o| options[:dimension] = o.to_i }
  opt.on('-f', '--folder FOLDER') { |o| options[:folder] = o.to_s }
end.parse!

# Constants
EPSILON = 1e-10
ORDINALS = {
  '1': 'st',
  '2': 'nd',
  '3': 'rd'
}.freeze
VARIABLES = %w[x y z w k a b c d e f g h i j k l].freeze
SEPARATOR_SIZE = 15
OUTPUT_FOLDER = options[:folder] || 'output_folder'
ITERATIONS = options[:iterations] || 250_000
MATRIX_DIMENSION = options[:dimension] || 4

# Prints a new line
def print_new_line
  puts ''
end

# Creates a separator
def print_separator(separator = '-', separator_size = SEPARATOR_SIZE)
  print_new_line
  puts separator * separator_size
  print_new_line
end

# Receives a number and prints it with an ordinal termination
def format_ordinal(number)
  number.to_s + ORDINALS.fetch(number.to_s[-1].to_sym, 'th')
end

# Pretty-print the matrix in a custom format
def pp_matrix(matrix)
  matrix.each { |x| puts x.map { |y| y.inspect[1...-1].split('').join(' ') + ' , ' }.join[0...-3] }
  print_new_line
end

# Pretty-print the vector in a custom format
def pp_vector(vector)
  puts vector.map { |y| y.inspect[1...-1].split('').join(' ') + ' , ' }.join[0...-3]
  print_new_line
end

# Performs an in-place Gaussian elimination on an NxN matrix 'matrix' (2D array
# of Numeric objects) and an N-element vector (array of N Numerics) placed as a
# column-vector in the Matrix.
def gaussian_elimination(matrix)
  0.upto(matrix.length - 2) do |pivot_idx|
    # Find the best pivot. This is the one who has the largest absolute value
    # relative to his row (scaled partial pivoting). This step can be omitted
    # to improve speed at the cost of increased error.

    puts "For the #{format_ordinal pivot_idx + 1} row, find the best pivot"
    max_rel_val = 0
    max_idx = pivot_idx
    pivot_idx.upto(matrix.length - 1) do |row|
      rel_val = matrix[row][pivot_idx] / matrix[row].map(&:abs).max
      if rel_val > max_rel_val
        max_rel_val = rel_val
        max_idx = row
      end
    end

    if pivot_idx != max_idx
      puts "Change #{format_ordinal pivot_idx + 1} row with #{format_ordinal max_idx + 1}"

      # Swap the best pivot row into place.
      matrix[pivot_idx], matrix[max_idx] = matrix[max_idx], matrix[pivot_idx]
    else
      puts "We don't need to change any row, as the current row has the best pivot"
    end

    pp_matrix matrix
    print_new_line

    pivot = matrix[pivot_idx][pivot_idx]
    # Loop over each row below the pivot row.
    (pivot_idx + 1).upto(matrix.length - 1) do |row|
      # Find factor so that [this row] = [this row] - factor*[pivot row]
      # leaves 0 in the pivot column.
      factor = pivot != 0 ? matrix[row][pivot_idx] / pivot : 0

      next unless factor != 0

      puts "Cancel the #{format_ordinal pivot_idx + 1} coefficient in #{format_ordinal row + 1}" \
          " row: R#{row + 1} <- R#{row + 1} #{factor >= 0 ? '-' : '+'} " \
          "( #{factor.abs.to_s.split('').join(' ')} ) * R#{pivot_idx + 1}"

      # We know it will be zero.
      matrix[row][pivot_idx] = 0r

      # Compute [this row] = [this row] - factor * [pivot row] for the other cols.
      (pivot_idx + 1).upto(matrix[row].length - 1) do |col|
        matrix[row][col] -= factor * matrix[pivot_idx][col]
      end
    end

    print_new_line
    puts 'After it, this is the new matrix:'
    pp_matrix matrix
    print_separator
  end

  matrix
end

# Assumes 'matrix' is in row echelon form.
def back_substitution(matrix)
  (matrix.length - 1).downto(0) do |pivot_idx|
    # Multiply the current vector position by the pivot_idx inverse (1/pivot_idx)
    inverse = 1 / matrix[pivot_idx][pivot_idx]
    matrix[pivot_idx][-1] *= inverse
    matrix[pivot_idx][pivot_idx] = 1r # We know it will be 1
    puts "Multiply the #{format_ordinal pivot_idx + 1} row by its diagonal inverse: "\
         "#{inverse.to_s.split('').join(' ')}"

    if (pivot_idx - 1).negative?
      puts 'And we don\'t have to zero any row'
    else
      puts 'We iterate over the rows above the current pivot index, to zero them'
      print_new_line
      (pivot_idx - 1).downto(0) do |row|
        if !matrix[row][pivot_idx].zero?
          puts "Cancel R#{row + 1} #{format_ordinal row + 1} coefficient: " \
              "R#{row + 1} <- R#{row + 1} #{matrix[row][pivot_idx] >= 0 ? '-' : '+'} " \
              "( #{matrix[row][pivot_idx].abs.to_s.split('').join(' ')} ) * R#{pivot_idx + 1}"

          matrix[row][-1] -= matrix[row][pivot_idx] * matrix[pivot_idx].last
          matrix[row][pivot_idx] = 0r # We know it will be 0
        else
          puts "The #{format_ordinal row + 1} coefficient in R#{row + 1} is already zeroed, " \
              'so we follow along'
        end
      end
    end

    print_new_line
    puts 'After it, this is the matrix'
    pp_matrix matrix
    print_separator
  end

  puts 'And in the reduced row echelon form we have:'
  pp_matrix matrix
  print_separator

  matrix
end

# Calculate the determinant, and if it is zero, return true
def determinant_zero(matrix)
  puts 'We calculate the matrix determinant to see if it is singular or not'
  det = Matrix[*matrix].determinant

  if det.zero?
    puts 'As the determinant is zero, this matrix is singular, so it has infinite solutions'
  else
    puts "As the determinant is #{det.denominator == 1 ? det.numerator.to_s.split('').join(' ') : det}" \
         ', the matrix is NOT singular, so we can procceed'
  end
  print_separator

  det.zero?
end

# Print the result.
def print_result(matrix)
  puts 'With the matrix reduced to their reduced row echelon form, we have that the result' \
       ' for the variables are:'
  puts(matrix.map(&:last)
             .each_with_index
             .map { |variable, idx| "#{VARIABLES[idx]} = #{variable.to_s.split('').join(' ')}" }
             .reduce { |acc, new| "#{acc}, #{new}" })
end

# Generates a random matrix
def generate_matrix
  generator = Rubystats::NormalDistribution.new(0, 3)
  numbers = (MATRIX_DIMENSION * (MATRIX_DIMENSION + 1))
            .times
            .map { Rational(generator.rng.to_i) }
            .each_slice(MATRIX_DIMENSION)
            .to_a

  matrix = numbers[0...-1]
  answer = numbers[-1]

  vector = solve_equation(matrix, answer)

  [matrix, vector]
end

# Solves an equation
def solve_equation(matrix, coefficients)
  matrix.map do |row|
    sum = 0
    row.each_with_index do |value, idx|
      sum += value * coefficients[idx]
    end

    sum
  end
end

# Solves a system of equations: matrix * X = vector
def iterate(matrix, vector)
  # Print the equation
  puts 'Given the following equation, we want to solve it'
  print_equation(matrix, vector)
  print_new_line

  # Print the matrix and the vector used to solve it
  puts 'First we write a matrix with the equation coefficients, and a vector with the solutions:'
  pp_matrix matrix
  pp_vector vector
  print_separator

  # Calculate the determinant, and if it is zero, stop the linear_equation solver
  return if determinant_zero(matrix)

  # Add the vector as the last column-vector of the matrix
  puts 'We will use our vector soluction, as the last column-vector of the matrix'
  vector.each_with_index { |val, idx| matrix[idx] << val }
  pp_matrix matrix

  # Performs Gaussian elemination to put the system in row echelon form.
  print_separator
  puts 'We reduce our matrix to their row echelon form:'
  print_new_line
  gaussian_elimination(matrix)

  # Performs Back-substitution to solve the system.
  puts 'Then, we reduce to their reduced row echelon form:'
  print_new_line
  back_substitution(matrix)

  # Prints the final result
  print_result(matrix)
end

# Returns the signnumber
def signal(number)
  number.negative? ? ' - ' : ' + '
end

# Prints an equation based on its matrix and vector
def print_equation(matrix, vector)
  matrix.each_with_index do |row, row_idx|
    print row[0].negative? ? '- ' : '  '
    row.each_with_index do |value, col_idx|
      print "#{value.abs.to_s.split('').join(' ')} #{VARIABLES[col_idx]}" \
            "\t#{col_idx + 1 < row.length ? signal(row[col_idx + 1]) : ''}"
    end
    puts " = #{vector[row_idx].to_s.split('').join(' ')}"
  end
end

# Create the folder
FileUtils.mkdir OUTPUT_FOLDER unless File.directory? OUTPUT_FOLDER

# Generate the systems
missed = 0
ITERATIONS.times do |index|
  warn "Starting #{index}"
  filename = "./#{OUTPUT_FOLDER}/#{index}.txt"
  $stdout.reopen(filename, 'w')

  begin
    iterate(*generate_matrix)
  rescue ZeroDivisionError
    missed += 1
    warn "Error at index #{index}... Skipping and deleting file..."
    File.delete(filename) if File.exist?(filename)
  end
end

warn "Completed #{ITERATIONS - missed}/#{ITERATIONS} -> #{(ITERATIONS - missed).to_f / ITERATIONS}%"
