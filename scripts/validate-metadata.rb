#!/usr/bin/env ruby
# Basic repository consistency checks, not a replacement for Palomar validation.
require "yaml"

root = File.expand_path("..", __dir__)
data = YAML.safe_load(File.read(File.join(root, "formalization.yaml")), aliases: false)
abort "formalization.yaml must be a mapping" unless data.is_a?(Hash)
abort "formalization.yaml must use v0.4" unless data["version"] == "v0.4"

project = data.fetch("project")
%w[name description license].each do |key|
  value = project[key]
  abort "project.#{key} must be nonempty" unless value.is_a?(String) && !value.strip.empty?
end
%w[authors responsible_maintainers].each do |key|
  values = project[key]
  unless values.is_a?(Array) && !values.empty? && values.all? { |value| value.is_a?(String) && !value.strip.empty? }
    abort "project.#{key} must list responsible humans"
  end
end
abort "project.license must match the Apache-2.0 LICENSE" unless project["license"] == "Apache-2.0"
license = File.read(File.join(root, "LICENSE"))
unless license.include?("Apache License") && license.include?("Version 2.0, January 2004")
  abort "LICENSE is not the expected Apache 2.0 text"
end

sources = data["sources"]
abort "sources must be nonempty" unless sources.is_a?(Array) && !sources.empty?
relationships = %w[formalizes adapts independently-proves background other]
source_types = ["paper", "book", "web discussion", "folklore", "original-proof", "other"]
sources.each do |source|
  abort "each source needs a title" unless source["title"].is_a?(String) && !source["title"].strip.empty?
  abort "invalid source relationship" unless relationships.include?(source["relationship"])
  abort "invalid source type" if source.key?("type") && !source_types.include?(source["type"])
  location = source["location"]
  if location.is_a?(String) && location.start_with?("docs/") && !File.file?(File.join(root, location))
    abort "missing cited local source: #{location}"
  end
end
if sources.any? { |source| source["type"] == "original-proof" }
  abort "original-result sources need background/other relationships" unless sources.all? { |source| %w[background other].include?(source["relationship"]) }
else
  abort "source-based metadata needs a formalized source" unless sources.any? { |source| %w[formalizes adapts independently-proves].include?(source["relationship"]) }
end

status = data.fetch("status")
abort "status.proof_status must be explicit" unless %w[in_progress complete].include?(status["proof_status"])
%w[sorry_count sorry_in_definitions].each do |key|
  abort "status.#{key} must be a nonnegative integer" unless status[key].is_a?(Integer) && status[key] >= 0
end
completed = status.fetch("completed_main_results", [])
abort "completed_main_results must be a list" unless completed.is_a?(Array)
abort "completed_main_results must not contain duplicates" unless completed.uniq == completed
abort "in-progress status requires an explicit scope" if status["scope"].to_s.strip.empty?
abort "automation.methods must be nonempty" if data.fetch("automation").fetch("methods").empty?
abort "review.status must be nonempty" if data.fetch("review").fetch("status").strip.empty?
puts "Metadata is structurally consistent; proof status: #{status['proof_status']}."
puts "This check does not establish theorem completion or registry eligibility."
