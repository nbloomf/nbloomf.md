BEGIN {
  # Use quoted CSV field convention
  FPAT = "([^,]+)|(\"[^\"]+\")"
}


/Prompt/ {
  print "& Prompt & SD & D & U & A & SA & Mean \\\\ \\hline";
  print "";
}


/\"/ {
  # Print the line number less 1 (for the header row) 
  printf NR-1 ". & ";

  # Extract question text (sans quotes)
  print substr($1, 2, length($1)-2) " &";

  # Print response counts (note the order)
  printf " " $6 " & " $5 " & " $4 " & " $3 " & " $2 " & ";

  # Calculate and print the mean
  weighted_sum = $2 + 0.75*$3 + 0.5*$4 + 0.25*$5 + 0*$6;
  rating_count = $2 +      $3 +     $4 +      $5 +   $6;
  mean_rating = int(100 * weighted_sum / rating_count);
  print mean_rating "\\% \\\\";

  print "";
}
