package Census::US;
$Census::US::VERSION = '0.01';

use strict;
use warnings;
use Carp;
use IO::File;
use LWP::UserAgent;
use Text::CSV_XS;
use DBI;
use Data::Dumper;
use Archive::Zip qw( :ERROR_CODES :CONSTANTS );
use File::Basename;
use File::Copy;
use XML::Twig;
use Safe;
use File::Spec;

my $default_directory = "~/.census-us";

my %state_from_postal_code =
  (
   AL => ["Alabama", 1, 1],
   AK => ["Alaska", 1, 0],
   AS => ["American Samoa", 0, 0],
   AZ => ["Arizona", 1, 1],
   AR => ["Arkansas", 1, 1],
   CA => ["California", 1, 1],
   CO => ["Colorado", 1, 1],
   CT => ["Connecticut", 1, 1],
   DE => ["Delaware", 1, 1],
   DC => ["District of Columbia", 1, 1],
   FL => ["Florida", 1, 1],
   GA => ["Georgia", 1, 1],
   GU => ["Guam", 0, 0],
   HI => ["Hawaii", 1, 0],
   ID => ["Idaho", 1, 1],
   IL => ["Illinois", 1, 1],
   IN => ["Indiana", 1, 1],
   IA => ["Iowa", 1, 1],
   KS => ["Kansas", 1, 1],
   KY => ["Kentucky", 1, 1],
   LA => ["Louisiana", 1, 1],
   ME => ["Maine", 1, 1],
   MD => ["Maryland", 1, 1],
   MH => ["Marshall Islands", 0, 0],
   MA => ["Massachusetts", 1, 1],
   MI => ["Michigan", 1, 1],
   FM => ["Micronesia", 0, 0],
   MN => ["Minnesota", 1, 1],
   MS => ["Mississippi", 1, 1],
   MO => ["Missouri", 1, 1],
   MT => ["Montana", 1, 1],
   NE => ["Nebraska", 1, 1],
   NV => ["Nevada", 1, 1],
   NH => ["New Hampshire", 1, 1],
   NJ => ["New Jersey", 1, 1],
   NM => ["New Mexico", 1, 1],
   NY => ["New York", 1, 1],
   NC => ["North Carolina", 1, 1],
   ND => ["North Dakota", 1, 1],
   MP => ["Northern Marianas", 0, 0],
   OH => ["Ohio", 1, 1],
   OK => ["Oklahoma", 1, 1],
   OR => ["Oregon", 1, 1],
   PW => ["Palau", 0, 0],
   PA => ["Pennsylvania", 1, 1],
   PR => ["Puerto Rico", 0, 0],
   RI => ["Rhode Island", 1, 1],
   SC => ["South Carolina", 1, 1],
   SD => ["South Dakota", 1, 1],
   TN => ["Tennessee", 1, 1],
   TX => ["Texas", 1, 1],
   US => ["United States", 0, 1],
   UT => ["Utah", 1, 1],
   VT => ["Vermont", 1, 1],
   VA => ["Virginia", 1, 1],
   VI => ["Virgin Islands", 0, 0],
   WA => ["Washington", 1, 1],
   WV => ["West Virginia", 1, 1],
   WI => ["Wisconsin", 1, 1],
   WY => ["Wyoming", 1, 1],
);

my %postal_code_from_state =
  (
   (map {$state_from_postal_code{$_}->[0] => $_} keys %state_from_postal_code),
   (map {uc($state_from_postal_code{$_}->[0]) => $_} keys %state_from_postal_code),
  );

my %fips_from_postal_code =
  (
   AK => 2,
   MN => 27,
   CT => 9,
   VT => 50,
   DC => 11,
   NM => 35,
   IL => 17,
   MD => 24,
   OH => 39,
   NV => 32,
   IA => 19,
   MA => 25,
   DE => 10,
   FL => 12,
   MS => 28,
   CA => 6,
   VA => 51,
   WA => 53,
   MT => 30,
   NJ => 34,
   SD => 46,
   AZ => 4,
   CO => 8,
   KY => 21,
   HI => 15,
   LA => 22,
   RI => 44,
   ID => 16,
   ND => 38,
   TX => 48,
   MO => 29,
   AL => 1,
   NC => 37,
   GA => 13,
   WY => 56,
   OK => 40,
   UT => 49,
   NH => 33,
   OR => 41,
   WI => 55,
   SC => 45,
   PR => 72,
   MI => 26,
   NY => 36,
   AR => 5,
   WV => 54,
   PA => 42,
   TN => 47,
   IN => 18,
   NE => 31,
   ME => 23,
   KS => 20,
   US => 0,
);

my %postal_code_from_fips = reverse %fips_from_postal_code;
my %state_from_fips = map {$_ => $state_from_postal_code{$postal_code_from_fips{$_}}} keys %postal_code_from_fips;


my @possible_boundary_years = qw/2000 2008 2009 2010 2011 2012 2013/;

my %sum_level_2010_of =
  (
   tract                   => "140_00",
   block_group             => "150_00",
   congressional_districts => "500_11",
   county_sub              => "060_00",
   place                   => "160_00",
   state_legis_upper       => "610_u2",
   state_legis_lower       => "620_l2",
   school_unified          => "970_00",
   school_elementary       => "950_00",
   school_secondary        => "960_00",
   voting_district         => "700_00",
  );

my %sum_level_of =
  (
   state                   => "040",
   county                  => "050",
   tract                   => "140",
   block_group             => "150",
   congressional_districts => "500",
   county_sub              => "060",
   place                   => "160",
   state_legis_upper       => "610",
   state_legis_lower       => "620",
   school_unified          => "970",
   school_elementary       => "950",
   school_secondary        => "960",
   voting_district         => "700",
   zip                     => "860",
   citycouncil             => "990",
   schoolcatchment         => "991",
  );

my %level_key =
  (
   'block'       => '101',
   'block_group' => '150',
   'citycouncil' => '990',
   'schoolcatchment' => '991',
   'congressional_districts' => '500',
   'county'      => '050',
   'county_sub'  => '060',
   'place'                   => '160',
   'school_elementary'       => '950',
   'school_secondary'        => '960',
   'school_unified'          => '970',
   'state'       => '040',
   'state_legis_lower'       => '620',
   'state_legis_upper'       => '610',
   'tract'       => '140',
   'voting_district'         => '700',
   'zip'         => '860',
  );

my %rev_level_key = reverse %level_key;

my %sum_level_names =
  (
   state                   => "States",
   county                  => "Counties",
   tract                   => "Census Tracts",
   block_group             => "Block Groups",
   congressional_districts => "Cong. Districts",
   county_sub              => "County Subdivisions",
   place                   => "Census Places",
   state_legis_upper       => "State Legis. Upper",
   state_legis_lower       => "State Legis. Lower",
   school_unified          => "Unif. Sch. Dists.",
   school_elementary       => "Elem. Sch. Dists.",
   school_secondary        => "Secondary Sch. Dists.",
   voting_district         => "Voting Districts",
   zip                     => "Zip Codes",
   citycouncil             => "City Council Districts",
   schoolcatchment         => "School Catchment",
  );

my %sum_level_key = reverse %sum_level_names;

my %tiger_code_of =
  (
   tract       => "tract",
   block_group => "bg",
   block       => "tabblock",
   county_sub  => "cousub",
  );

my %simplify_factor =
  (
   block                   => 0.001,
   block_group             => 0.001,
   citycouncil             => 0.001,
   schoolcatchment         => 0.001,
   congressional_districts => 0.001,
   county                  => 0.001,
   county_sub              => 0.001,
   place                   => 0.001,
   school_elementary       => 0.001,
   school_secondary        => 0.001,
   school_unified          => 0.001,
   state                   => 0.001,
   state_legis_lower       => 0.001,
   state_legis_upper       => 0.001,
   tract                   => 0.0001,
   voting_district         => 0.001,
   zip                     => 0.001,
  );

my %cols_for_level =
  (
   block                   => [qw/STATE COUNTY TRACT BLKGRP BLOCK/],
   block_group             => [qw/STATE COUNTY TRACT BLKGRP/],
   citycouncil             => [qw/DIST_NUM/],
   schoolcatchment         => [qw/NAME2/],
   congressional_districts => [qw/STATE CDCURR/],
   county                  => [qw/STATE COUNTY/],
   county_sub              => [qw/STATE COUNTY COUSUB/],
   place                   => [qw/STATE/],
   school_elementary       => [qw/STATE/],
   school_secondary        => [qw/STATE/],
   school_unified          => [qw/STATE SDUNI/],
   state                   => [qw/STATE/],
   state_legis_lower       => [qw/STATE SLDL/],
   state_legis_upper       => [qw/STATE SLDU/],
   tract                   => [qw/STATE COUNTY TRACT/],
   voting_district         => [qw/STATE COUNTY VTD/],
   zip                     => [qw/ZCTA5/],
  );

sub get_sum_level_of{
  my ($self, $level) = @_;
  return ($sum_level_of{$level}) if ($sum_level_of{$level});
  return ($sum_level_of{$sum_level_key{$level}}) if ($sum_level_of{$sum_level_key{$level}});
  warn "level is $level";
  return ($level);
}

my %trans_geo_data =
  (
   STATEFP00  => "STATE",
   STATEFP10  => "STATE",
   COUNTYFP00 => "COUNTY",
   COUSUBFP00 => "COUSUB",
   STATEFP    => "STATE",
   COUNTYFP   => "COUNTY",
   COUSUBFP   => "COUSUB",
   TRACTCE    => "TRACT",
   TRACTCE00  => "TRACT",
   TRACTCE10  => "TRACT",
   GEOID      => "FIPS",
   GEOID10    => "FIPS",
   NAMELSAD   => "NAME1",
   NAMELSAD00 => "NAME1",
   NAMELSAD10 => "NAME1",
   MTFCC      => "MTFCC",
   MTFCC00    => "MTFCC",
   MTFCC10    => "MTFCC",
   FUNCSTAT   => "FUNCSTAT",
   FUNCSTAT00 => "FUNCSTAT",
   FUNCSTAT10 => "FUNCSTAT",
   ALAND      => "AREA_LAND",
   AWATER     => "AREA_WATER",
   ALAND00    => "AREA_LAND",
   ALAND10    => "AREA_LAND",
   AWATER00   => "AREA_WATER",
   AWATER10   => "AREA_WATER",
   INTPTLAT   => "LATITUDE",
   INTPTLON   => "LONGITUDE",
   INTPTLAT00 => "LATITUDE",
   INTPTLON00 => "LONGITUDE",
   INTPTLAT10 => "LATITUDE",
   INTPTLON10 => "LONGITUDE",
   GEO_ID     => "FIPS",
   CTIDFP00   => "FIPS",
   STATE      => "STATE",
   COUNTY     => "COUNTY",
   LSAD       => "NAME3",
   CENSUSAREA => "CENSUS_AREA",
   Name       => "NAME2",
   AREA       => "AREA",
   PERIMETER  => "PERIMETER",
   LSAD_TRANS => "TYPE",
   NAME00     => "NAME2",
   ZCTA5CE10  => "ZCTA5",
   CLASSFP00  => "CLASSFP",
   CLASSFP10  => "CLASSFP",
   PARTFLG00  => "PARTFLG",
   PARTFLG10  => "PARTFLG",
   CD         => "CDCURR",
  );

sub col_trans_table {
  return(\%trans_geo_data);
}

sub fetch_boundary{
  my $self = shift;
  my %args = @_;
  $args{postal_code} //= get_postal_code_from_state($args{state});
  $args{boundary_year} //= 2010;
  $args{sumlevel} //= $self->get_sum_level_of($args{level});
  my %info;
  my $level = $rev_level_key{$args{sumlevel}};

  warn "Sum level is $args{sumlevel} and level is $args{level} and level is $level";

  $info{sumlevel} = $args{sumlevel};
  my $directory = $args{directory} // $self->get_directory() // glob($default_directory);
  $directory .= "/shapefiles";
  unless (-d $directory){
    mkdir($directory) or croak "Could not create $directory";
  }
  $directory .= "/" . uc($args{postal_code});
  unless (-d $directory){
    mkdir($directory) or croak "Could not create $directory";
  }
  my $kml_file = "$directory/boundary_" . $level . "_" . $args{boundary_year} . ".kml";
  print STDERR "KML file is $kml_file\n";
  my $url = $self->boundary_url(%args);
  my $zip_file = $url;
  $zip_file =~ s/.*\///;
  $zip_file = "$directory/$zip_file";
  unless (-f $zip_file){
    print STDERR "Getting URL $url\n";
    my $ua = LWP::UserAgent->new();
    my $response = $ua->get($url, ':content_file' => $zip_file);
    croak $response->status_line unless ($response->is_success);
  }
  my $zip = Archive::Zip->new();
  croak "Could not read zip file $zip_file" unless ( $zip->read( $zip_file ) == AZ_OK );
  my ($shapefile) = map {$_->fileName()} $zip->membersMatching('.*\.shp$');
  croak "Could not find shapefile in zip" unless ($shapefile);
  unless (-f $kml_file && -f $shapefile){
    my $shapefilepath = File::Spec->catfile($directory, $shapefile);
    warn "Directory is $directory and shapefile is $shapefile";
    croak "Could not extract files" unless ( $zip->extractTree(undef, File::Spec->catfile($directory, '')) == AZ_OK );
    my $command = qq{ogr2ogr -simplify $simplify_factor{$level} -f "KML" "$kml_file.part" "$shapefilepath"};
    print STDERR "Command is $command\n";
    system($command) and croak "Failed to convert $shapefile to $kml_file using ogr2ogr";
    #if (-f $zip_file){
    #  unlink ($zip_file) or croak "Could not delete $zip_file";
    #}
    move($kml_file . '.part', $kml_file) or croak "Could not move $kml_file into place";
  }
  my (%okcounty, $no_check, %fips_done);
  #print STDERR "County is $args{county}\n";
  if ($args{county}){
    if (ref($args{county})){
      croak "Invalid county" unless (ref($args{county}) eq "ARRAY");
      if (scalar(@{$args{county}})){
	foreach my $county (@{$args{county}}){
	  $okcounty{sprintf('%03d', $county)} = 1;
	}
      }
      else{
	$no_check = 1;
      }
    }
    else{
      $okcounty{sprintf('%03d', $args{county})} = 1;
    }
  }
  else{
    $no_check = 1;
  }
  #print STDERR "Parsing KML file where level is $level and okcounty is " . Dumper(\%okcounty) . "\n";
  $info{cols_for_fips} = [@{$cols_for_level{$level}}];
  warn "Setting cols_for_fips to " . join(', ', @{$info{cols_for_fips}});
  $info{trans_table} = $self->col_trans_table();
  my $twig = XML::Twig->new
    (
     twig_handlers =>
     {
      Placemark => sub {
	my $placemark = $_;
	my %result;
	#print STDERR "Found a placemark called " . $placemark->first_child('name')->text() . "\n";
	my $schemadata = $placemark->first_child('ExtendedData')->first_child('SchemaData');
	$result{SCHEMA_URL} = $schemadata->att('schemaUrl');
	foreach my $dataitem ($schemadata->children('SimpleData')){
	  $result{$trans_geo_data{$dataitem->att('name')} // $dataitem->att('name')} = $dataitem->text();
	}
	foreach my $polygon ($placemark->children('Polygon')){
	  push(@{$result{POLYGON}}, $polygon->sprint());
	  #print STDERR "Found polygon\n";
	}
	foreach my $polygon ($placemark->children('MultiGeometry')){
	  push(@{$result{POLYGON}}, $polygon->sprint());
	}
	$result{FIPS} = join('', map {$result{$_} // 'ERROR'} @{$cols_for_level{$level}});
	$result{FIPS} =~ s/.*US//;
	$result{FIPS} = $args{sumlevel} . '00US' . $result{FIPS};
	#print STDERR "FIPS is $result{FIPS} and no_check is $no_check and county is $result{COUNTY}\n";
	return unless ($no_check || !defined($result{COUNTY}) || $okcounty{$result{COUNTY}});
	if ($args{result}->{$result{FIPS}} && $args{result}->{$result{FIPS}}->{boundarydone}){
	  print STDERR "Boundary already loaded for $result{FIPS}, not adding again.\n";
	  return;
	}
	if (exists($args{result}->{$result{FIPS}}) || $args{show_all}){
	  if ($args{result}->{$result{FIPS}}->{boundary}){
	    foreach my $key (qw/AREA PERIMETER/){
	      $args{result}->{$result{FIPS}}->{boundary}->{$key} += $result{$key} if ($result{$key});
	    }
	    push(@{$args{result}->{$result{FIPS}}->{boundary}->{POLYGON}}, @{$result{POLYGON}}) if ($result{POLYGON});
	  }
	  else{
	    $args{result}->{$result{FIPS}}->{boundary} = \%result;
	  }
	  $fips_done{$result{FIPS}} = undef;
	}
	else{
	  print STDERR "No result found for $result{FIPS}, not adding boundary.\n";
	}
      },
     },
     pretty_print => 'none',
     empty_tags => 'html',
    );
  $twig->parsefile($kml_file);
  $twig->purge();
  while (my ($key, undef) = each %fips_done){
    $args{result}->{$key}->{boundarydone} = 1;
  }
  return($shapefile, $directory, \%info);
}

sub boundary_url{
  my $self = shift;
  my %args = @_;
  my $level = $rev_level_key{$args{sumlevel}};
  my $state_fips = sprintf('%02d', $fips_from_postal_code{$args{postal_code}});
  $state_fips = "us" if ($state_fips eq '00');
  if($level eq "citycouncil"){
    return("http://www.pasda.psu.edu/philacity/data/PhiladelphiaCouncilDistricts_2000.zip");
  }
  if($level eq "tract" && $args{boundary_year} eq "2000"){
    return("ftp://ftp2.census.gov/geo/tiger/TIGER2010/TRACT/2000/tl_2010_" . $state_fips . "_tract00.zip");
  }
  if($tiger_code_of{$level}){
    return("ftp://ftp2.census.gov/geo/tiger/TIGER2011/" . uc($tiger_code_of{$level}) . "/tl_2011_" . $state_fips . "_" . $tiger_code_of{$level} . ".zip");
  }
  if($level eq "state" && $args{postal_code} eq "US"){
    return("http://www2.census.gov/geo/tiger/GENZ2010/gz_2010_us_040_00_500k.zip");
  }
  if($level eq "county" && $args{postal_code} eq "US"){
    return("http://www2.census.gov/geo/tiger/GENZ2010/gz_2010_us_050_00_500k.zip");
  }
  if ($sum_level_2010_of{$level}){
    return("http://www2.census.gov/geo/tiger/GENZ2010/gz_2010_" . $state_fips . "_" . $sum_level_2010_of{$level} . "_500k.zip");
  }
  if($level eq "county"){
    return("http://www2.census.gov/geo/tiger/PREVGENZ/co/co00shp/co" . $state_fips . "_d00_shp.zip");
  }
  if($level eq "schoolcatchment"){
    return("http://www.litigationdatabase.org/phila-school-catchment-areas.zip");
  }
  if($level eq "zip"){
#Alternative: http://www.census.gov/geo/cob/bdy/zt/z500shp/zt42_d00_shp.zip
    my $yr = $args{boundary_year};
    $yr = '2009' if ($yr < 2009);
    $yr = '2010' if ($yr > 2010);
    if ($yr eq '2009'){
      return("ftp://ftp2.census.gov/geo/tiger/TIGER" . $yr . "/" . state_name(%args, underscore => 1, of => 'upper') . "tl_" . $yr . "_" . $state_fips . "_zcta5.zip");
    }
    else{
      return("ftp://ftp2.census.gov/geo/tiger/TIGER" . $yr . "/ZCTA5/" . $yr . "/tl_" . $yr . "_" . $state_fips . "_zcta510.zip");
    }
  }
  croak "Could not get boundary url for $args{sumlevel} and $args{postal_code}";
}

my %geo_url_of =
  (
   census_2000 =>
   {
    sf1 => sub{my %args = @_; return("http://www2.census.gov/census_2000/datasets/Summary_File_1/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "geo_uf1.zip", lc($args{postal_code}) . "geo.uf1");},
    sf2 => sub{my %args = @_; return("http://www2.census.gov/census_2000/datasets/Summary_File_2/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "geo_uf2.zip", lc($args{postal_code}) . "geo.uf2");},
    sf3 => sub{my %args = @_; return("http://www2.census.gov/census_2000/datasets/Summary_File_3/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "geo_uf3.zip", lc($args{postal_code}) . "geo.uf3");},
    sf4 => sub{my %args = @_; return("http://www2.census.gov/census_2000/datasets/Summary_File_4/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "geo_uf4.zip", lc($args{postal_code}) . "geo.uf4");},
   },
  );

my %lookup_file_of =
  (
   census_2000 =>
   {
    sf1 => "Decennial2000SF1.pm",
    sf2 => "Decennial2000SF2.pm",
    sf3 => "Decennial2000SF3.pm",
    sf4 => "Decennial2000SF4.pm",
   },
   census_2010 =>
   {
    sf1 => "Decennial2010SF1.pm",
    sf2 => "Decennial2010SF2.pm",
   }
  );

my %data_url_of =
  (
   acs => sub{my %args = @_; return($args{by_state_by_sequence_url}->(%args) . $args{endyear} . $args{years} . lc($args{postal_code}) . sprintf('%04d%03d', $args{segment}, 0) . '.zip');},
   census_2000 =>
   {
    sf1 => sub{my %args = @_; return(sprintf('http://www2.census.gov/census_2000/datasets/Summary_File_1/%s/%s%05d_uf1.zip', state_name(%args, underscore => 1, of => 'lower'), lc($args{postal_code}), $args{segment}));},
    sf2 => sub{my %args = @_; return(sprintf('http://www2.census.gov/census_2000/datasets/Summary_File_2/%s/%s%03d%02d_uf2.zip', state_name(%args, underscore => 1, of => 'lower'), lc($args{postal_code}), $args{iteration} || 1, $args{segment}));},
    sf3 => sub{my %args = @_; return(sprintf('http://www2.census.gov/census_2000/datasets/Summary_File_3/%s/%s%05d_uf3.zip', state_name(%args, underscore => 1, of => 'lower'), lc($args{postal_code}), $args{segment}));},
    sf4 => sub{my %args = @_; return(sprintf('http://www2.census.gov/census_2000/datasets/Summary_File_4/%s/%s%03d%02d_uf4.zip', state_name(%args, underscore => 1, of => 'lower'), lc($args{postal_code}), $args{iteration} || 1, $args{segment}));},
   },
   census_2010 =>
   {
    sf1 => sub{my %args = @_; return("http://www2.census.gov/census_2010/04-Summary_File_1/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "2010.sf1.zip", sprintf('%sgeo2010.sf1', lc($args{postal_code})));},
    sf2 => sub{my %args = @_; return("http://www2.census.gov/census_2010/05-Summary_File_2/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "2010.sf2.zip", sprintf('%sgeo2010.sf2', lc($args{postal_code})));},
    demographic_profile => sub{my %args = @_; return("http://www2.census.gov/census_2010/03-Demographic_Profile/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "2010.dp.zip", sprintf('%sgeo2010.dp', lc($args{postal_code})));},
    #demographic_profile_sf1 => sub{my %args = @_; return("http://www2.census.gov/census_2010/03-Demographic_Profile_with_SF1geos/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "20101.dp.zip", sprintf('%sgeo20101.dp', lc($args{postal_code})));},
    #advance_group_quarters => sub{my %args = @_; return("http://www2.census.gov/census_2010/02-Advance_Group_Quarters/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "2010.sgq.zip", sprintf('%sgeo2010.sgq', lc($args{postal_code})));},
    #redistricting => sub{my %args = @_; return("http://www2.census.gov/census_2010/01-Redistricting_File--PL_94-171/" . state_name(%args, underscore => 1, of => 'lower') . "/" . lc($args{postal_code}) . "2010.pl.zip", sprintf('%sgeo2010.pl', lc($args{postal_code})));},
   },
  );

my %data_file_of =
  (
   census_2010 =>
   {
    sf1 => sub{my %args = @_; return(sprintf('%s%05d2010.sf1', lc($args{postal_code}), $args{segment}));},
    sf2 => sub{my %args = @_; return(sprintf('%s%03d%02d2010.sf2', lc($args{postal_code}), $args{iteration} || 1, $args{segment}));},
    demographic_profile => sub{my %args = @_; return(sprintf('%s%05d2010.dp', lc($args{postal_code}), $args{segment}));},
    #demographic_profile_sf1 => sub{my %args = @_; return(sprintf('%s%05d20101.dp', lc($args{postal_code}), $args{segment}));},
    #advance_group_quarters => sub{my %args = @_; return(sprintf('%s%05d2010.sgq', lc($args{postal_code}), $args{segment}));},
    #redistricting => sub{my %args = @_; return(sprintf('%s%05d2010.pl', lc($args{postal_code}), $args{segment}));},
   },
   census_2000 =>
   {
    sf1 => sub{my %args = @_; return(sprintf('%s%05d.uf1', lc($args{postal_code}), $args{segment}));},
    sf2 => sub{my %args = @_; return(sprintf('%s%03d%02d.uf2', lc($args{postal_code}), $args{iteration} || 1, $args{segment}));},
    sf3 => sub{my %args = @_; return(sprintf('%s%05d.uf3', lc($args{postal_code}), $args{segment}));},
    sf4 => sub{my %args = @_; return(sprintf('%s%03d%02d.uf4', lc($args{postal_code}), $args{iteration} || 1, $args{segment}));},
   },
   acs => sub{my %args = @_; return($args{endyear} . $args{years} . lc($args{postal_code}) . sprintf('%04d%03d', $args{segment}, 0) . '.txt');},
  );

my %subset_names =
  (
   'sf1' => "Summary File 1",
   'sf2' => "Summary File 2",
   'sf3' => "Summary File 3",
  );

my %subset_key = reverse %subset_names;

sub corrected_subset {
  return ($_[0]) if ($subset_names{$_[0]});
  return ($subset_key{$_[0]});
}

my %dataset_names =
  (
   acs2009_1yr => 'ACS 2009, 1-year',
   acs2009_3yr => 'ACS 2009, 3-year',
   acs2009_5yr => 'ACS 2009, 5-year',
   acs2010_1yr => 'ACS 2010, 1-year',
   acs2010_3yr => 'ACS 2010, 3-year',
   acs2010_5yr => 'ACS 2010, 5-year',
   acs2011_1yr => 'ACS 2011, 1-year',
   acs2011_3yr => 'ACS 2011, 3-year',
   acs2011_5yr => 'ACS 2011, 5-year',
   acs2012_1yr => 'ACS 2012, 1-year',
   acs2012_3yr => 'ACS 2012, 3-year',
   acs2012_5yr => 'ACS 2012, 5-year',
   census_2000 => 'Census 2000',
   census_2010 => 'Census 2010',
  );

my %dataset_key = reverse %dataset_names;

sub corrected_dataset {
  return ($_[0]) if ($dataset_names{$_[0]});
  return ($dataset_key{$_[0]});
}

my %dataset_dispatch =
  (
   acs2009_1yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2009;
     $args{years} = 1;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2009_1yr/summaryfile/Entire_SF/20091YRSF.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2009_1yr/summaryfile/Entire_States/" . state_name(@_) . ".zip");};
     $args{by_state_by_sequence_url} = sub{my %args = @_; return("http://www2.census.gov/acs2009_1yr/summaryfile/Seq_By_ST/" . $args{postal_code} . "/");};
     $args{lookup_url} = "http://www2.census.gov/acs2009_1yr/summaryfile/UserTools/merge_5_6.txt";
     $args{geo_format} = "txt";
     return($self->fetch_acs(%args));
   },
   acs2009_3yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2009;
     $args{years} = 3;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2009_3yr/summaryfile/2007-2009_ACSSF_All_In_1_Giant_File(Experienced-Users-Only)/All_Geographies.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2009_3yr/summaryfile/2007-2009_ACSSF_By_State_All_Tables/" . state_name(@_) . "_All_Geographies.zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2009_3yr/summaryfile/2007-2009_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/");};
     $args{lookup_url} = "http://www2.census.gov/acs2009_3yr/summaryfile/UserTools/Sequence_Number_and_Table_Number_Lookup.txt";
     $args{geo_format} = "txt";
     return($self->fetch_acs(%args));
   },
   acs2009_5yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2009;
     $args{years} = 5;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2009_5yr/summaryfile/2005-2009_ACSSF_All_In_2_Giant_Files(Experienced-Users-Only)/" . acs_file_five_year(@_) . ".zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2009_5yr/summaryfile/2005-2009_ACSSF_By_State_All_Tables/" . state_name(@_) . "_" . acs_file_five_year(@_) . ".zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2009_5yr/summaryfile/2005-2009_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/" . acs_file_five_year(@_) . "/");};
     $args{lookup_url} = "http://www2.census.gov/acs2009_5yr/summaryfile/UserTools/Sequence_Number_and_Table_Number_Lookup.txt";
     $args{geo_format} = "txt";
     return($self->fetch_acs(%args));
   },
   acs2010_1yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2010;
     $args{years} = 1;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2010_1yr/summaryfile/2010_ACSSF_All_In_1_Giant_File(Experienced-Users-Only)/All_Geographies.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2010_1yr/summaryfile/2010_ACSSF_By_State_All_Tables/" . state_name(@_) . "_All_Geographies.zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2010_1yr/summaryfile/2010_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2010_3yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2010;
     $args{years} = 3;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2010_3yr/summaryfile/2008-2010_ACSSF_All_In_2_Giant_Files(Experienced-Users-Only)/All_Geographies.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2010_3yr/summaryfile/2008-2010_ACSSF_By_State_All_Tables/" . state_name(@_) . "_All_Geographies.zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2010_3yr/summaryfile/2008-2010_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2010_5yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2010;
     $args{years} = 5;
     $args{of} = "upper";
     $args{giant_url} = sub{return("http://www2.census.gov/acs2010_5yr/summaryfile/2006-2010_ACSSF_All_In_2_Giant_Files(Experienced-Users-Only)/" . acs_file_five_year(@_) . ".zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2010_5yr/summaryfile/2006-2010_ACSSF_By_State_All_Tables/" . state_name(@_) . "/" . acs_file_five_year(@_) . ".zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2010_5yr/summaryfile/2006-2010_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/" . acs_file_five_year(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2011_1yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2011;
     $args{years} = 1;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2011_1yr/summaryfile/2011_ACSSF_All_In_1_Giant_File(Experienced-Users-Only)/All_Geographies.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2011_1yr/summaryfile/2011_ACSSF_By_State_All_Tables/" . state_name(@_) . "_All_Geographies.zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2011_1yr/summaryfile/2011_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2011_3yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2011;
     $args{years} = 3;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2011_3yr/summaryfile/2009-2011_ACSSF_All_In_1_Giant_File(Experienced-Users-Only)/All_Geographies.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2011_3yr/summaryfile/2009-2011_ACSSF_By_State_All_Tables/" . state_name(@_) . "_All_Geographies.zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2011_3yr/summaryfile/2009-2011_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2011_5yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2011;
     $args{years} = 5;
     $args{of} = "upper";
     $args{giant_url} = sub{return("http://www2.census.gov/acs2011_5yr/summaryfile/2007-2011_ACSSF_All_In_2_Giant_Files(Experienced-Users-Only)/" . acs_file_five_year(@_) . ".tar.gz");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2011_5yr/summaryfile/2007-2011_ACSSF_By_State_All_Tables/" . state_name(@_) . "/" . acs_file_five_year(@_) . ".zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2011_5yr/summaryfile/2007-2011_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/" . acs_file_five_year(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2012_1yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2012;
     $args{years} = 1;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2012_1yr/summaryfile/2012_ACSSF_All_In_1_Giant_File(Experienced-Users-Only)/All_Geographies.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2012_1yr/summaryfile/2012_ACSSF_By_State_All_Tables/" . state_name(@_) . "_All_Geographies.zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2012_1yr/summaryfile/2012_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2012_3yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2012;
     $args{years} = 3;
     $args{giant_url} = sub{return("http://www2.census.gov/acs2012_3yr/summaryfile/2010-2012_ACSSF_All_In_1_Giant_File(Experienced-Users-Only)/All_Geographies.zip");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2012_3yr/summaryfile/2010-2012_ACSSF_By_State_All_Tables/" . state_name(@_) . "_All_Geographies.zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2012_3yr/summaryfile/2010-2012_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   acs2012_5yr => sub {
     my $self = shift;
     my %args = @_;
     $args{endyear} = 2012;
     $args{years} = 5;
     $args{of} = "upper";
     $args{giant_url} = sub{return("http://www2.census.gov/acs2012_5yr/summaryfile/2008-2012_ACSSF_All_In_2_Giant_Files(Experienced-Users-Only)/" . acs_file_five_year(@_) . ".tar.gz");};
     $args{by_state_all_tables_url} = sub{return("http://www2.census.gov/acs2012_5yr/summaryfile/2008-2012_ACSSF_By_State_All_Tables/" . state_name(@_) . "/" . acs_file_five_year(@_) . ".zip");};
     $args{by_state_by_sequence_url} = sub{return("http://www2.census.gov/acs2012_5yr/summaryfile/2008-2012_ACSSF_By_State_By_Sequence_Table_Subset/" . state_name(@_) . "/" . acs_file_five_year(@_) . "/");};
     return($self->fetch_acs(%args));
   },
   census_2000 => sub {
     my $self = shift;
     return($self->fetch_census_2000(@_));
   },
   census_2010 => sub {
     my $self = shift;
     return($self->fetch_census_2010(@_));
   },
  );

sub acs_file_five_year{
  my %args = @_;
  my $file;
  if (($args{level} && ($args{level} eq "tract" || $args{level} eq "block_group")) || ($args{sumlevel} && ($args{sumlevel} eq "140" || $args{sumlevel} eq "150"))){
    $file = "Tracts_Block_Groups_Only";
  }
  else{
    $file = "All_Geographies_Not_Tracts_Block_Groups";
  }
  return ($file);
}

my %geo_cols =
  (
   census_2000 =>
   [
    ['FILEID', 6, 1, 'text'],
    ['STUSAB', 2, 7, 'text'],
    ['SUMLEV', 3, 9, 'text'],
    ['GEOCOMP', 2, 12, 'text'],
    ['CHARITER', 3, 14, 'text'],
    ['CIFSN', 2, 17, 'text'],
    ['LOGRECNO', 7, 19, 'text'],
    ['REGION', 1, 26, 'text'],
    ['DIVISION', 1, 27, 'text'],
    ['STATECE', 2, 28, 'text'],
    ['STATE', 2, 30, 'text'],
    ['COUNTY', 3, 32, 'text'],
    ['COUNTYSC', 2, 35, 'text'],
    ['COUSUB', 5, 37, 'text'],
    ['COUSUBCC', 2, 42, 'text'],
    ['COUSUBSC', 2, 44, 'text'],
    ['PLACE', 5, 46, 'text'],
    ['PLACECC', 2, 51, 'text'],
    ['PLACEDC', 1, 53, 'text'],
    ['PLACESC', 2, 54, 'text'],
    ['TRACT', 6, 56, 'text'],
    ['BLKGRP', 1, 62, 'text'],
    ['BLOCK', 4, 63, 'text'],
    ['IUC', 2, 67, 'text'],
    ['CONCIT', 5, 69, 'text'],
    ['CONCITCC', 2, 74, 'text'],
    ['CONCITSC', 2, 76, 'text'],
    ['AIANHH', 4, 78, 'text'],
    ['AIANHHFP', 5, 82, 'text'],
    ['AIANHHCC', 2, 87, 'text'],
    ['AIHHTLI', 1, 89, 'text'],
    ['AITSCE', 3, 90, 'text'],
    ['AITS', 5, 93, 'text'],
    ['AITSCC', 2, 98, 'text'],
    ['ANRC', 5, 100, 'text'],
    ['ANRCCC', 2, 105, 'text'],
    ['MSACMSA', 4, 107, 'text'],
    ['MASC', 2, 111, 'text'],
    ['CMSA', 2, 113, 'text'],
    ['MACCI', 1, 115, 'text'],
    ['PMSA', 4, 116, 'text'],
    ['NECMA', 4, 120, 'text'],
    ['NECMACCI', 1, 124, 'text'],
    ['NECMASC', 2, 125, 'text'],
    ['EXI', 1, 127, 'text'],
    ['UA', 5, 128, 'text'],
    ['UASC', 2, 133, 'text'],
    ['UATYPE', 1, 135, 'text'],
    ['UR', 1, 136, 'text'],
    ['CD106', 2, 137, 'text'],
    ['CD108', 2, 139, 'text'],
    ['CD109', 2, 141, 'text'],
    ['CDCURR', 2, 143, 'text'],
    ['SLDU', 3, 145, 'text'],
    ['SLDL', 3, 148, 'text'],
    ['VTD', 6, 151, 'text'],
    ['VTDI', 1, 157, 'text'],
    ['ZCTA3', 3, 158, 'text'],
    ['ZCTA5', 5, 161, 'text'],
    ['SUBMCD', 5, 166, 'text'],
    ['SUBMCDCC', 2, 171, 'text'],
    ['AREALAND', 14, 173, 'text'],
    ['AREAWATR', 14, 187, 'text'],
    ['NAME', 90, 201, 'text'],
    ['FUNCSTAT', 1, 291, 'text'],
    ['GCUNI', 1, 292, 'text'],
    ['POP100', 9, 293, 'text'],
    ['HU100', 9, 302, 'text'],
    ['INTPTLAT', 9, 311, 'text'],
    ['INTPTLON', 10, 320, 'text'],
    ['LSADC', 2, 330, 'text'],
    ['PARTFLAG', 1, 332, 'text'],
    ['SDELM', 5, 333, 'text'],
    ['SDSEC', 5, 338, 'text'],
    ['SDUNI', 5, 343, 'text'],
    ['TAZ', 6, 348, 'text'],
    ['UGA', 5, 354, 'text'],
    ['PUMA5', 5, 359, 'text'],
    ['PUMA1', 5, 364, 'text'],
    ['RESERVE2', 15, 369, 'text'],
    ['MACC', 5, 384, 'text'],
    ['UACP', 5, 389, 'text'],
    ['RESERVED', 7, 394, 'text'],
   ],
   census_2010 =>
   [
    ['FILEID', 6, 1, 'text'],
    ['STUSAB', 2, 7, 'text'],
    ['SUMLEV', 3, 9, 'text'],
    ['GEOCOMP', 2, 12, 'text'],
    ['CHARITER', 3, 14, 'text'],
    ['CIFSN', 2, 17, 'text'],
    ['LOGRECNO', 7, 19, 'text'],
    ['REGION', 1, 26, 'text'],
    ['DIVISION', 1, 27, 'text'],
    ['STATE', 2, 28, 'text'],
    ['COUNTY', 3, 30, 'text'],
    ['COUNTYCC', 2, 33, 'text'],
    ['COUNTYSC', 2, 35, 'text'],
    ['COUSUB', 5, 37, 'text'],
    ['COUSUBCC', 2, 42, 'text'],
    ['COUSUBSC', 2, 44, 'text'],
    ['PLACE', 5, 46, 'text'],
    ['PLACECC', 2, 51, 'text'],
    ['PLACESC', 2, 53, 'text'],
    ['TRACT', 6, 55, 'text'],
    ['BLKGRP', 1, 61, 'text'],
    ['BLOCK', 4, 62, 'text'],
    ['IUC', 2, 66, 'text'],
    ['CONCIT', 5, 68, 'text'],
    ['CONCITCC', 2, 73, 'text'],
    ['CONCITSC', 2, 75, 'text'],
    ['AIANHH', 4, 77, 'text'],
    ['AIANHHFP', 5, 81, 'text'],
    ['AIANHHCC', 2, 86, 'text'],
    ['AIHHTLI', 1, 88, 'text'],
    ['AITSCE', 3, 89, 'text'],
    ['AITS', 5, 92, 'text'],
    ['AITSCC', 2, 97, 'text'],
    ['TTRACT', 6, 99, 'text'],
    ['TBLKGRP', 1, 105, 'text'],
    ['ANRC', 5, 106, 'text'],
    ['ANRCCC', 2, 111, 'text'],
    ['CBSA', 5, 113, 'text'],
    ['CBSASC', 2, 118, 'text'],
    ['METDIV', 5, 120, 'text'],
    ['CSA', 3, 125, 'text'],
    ['NECTA', 5, 128, 'text'],
    ['NECTASC', 2, 133, 'text'],
    ['NECTADIV', 5, 135, 'text'],
    ['CNECTA', 3, 140, 'text'],
    ['CBSAPCI', 1, 143, 'text'],
    ['NECTAPCI', 1, 144, 'text'],
    ['UA', 5, 145, 'text'],
    ['UASC', 2, 150, 'text'],
    ['UATYPE', 1, 152, 'text'],
    ['UR', 1, 153, 'text'],
    ['CDCURR', 2, 154, 'text'],
    ['SLDU', 3, 156, 'text'],
    ['SLDL', 3, 159, 'text'],
    ['VTD', 6, 162, 'text'],
    ['VTDI', 1, 168, 'text'],
    ['RESERVE2', 3, 169, 'text'],
    ['ZCTA5', 5, 172, 'text'],
    ['SUBMCD', 5, 177, 'text'],
    ['SUBMCDCC', 2, 182, 'text'],
    ['SDELM', 5, 184, 'text'],
    ['SDSEC', 5, 189, 'text'],
    ['SDUNI', 5, 194, 'text'],
    ['AREALAND', 14, 199, 'text'],
    ['AREAWATR', 14, 213, 'text'],
    ['NAME', 90, 227, 'text'],
    ['FUNCSTAT', 1, 317, 'text'],
    ['GCUNI', 1, 318, 'text'],
    ['POP100', 9, 319, 'text'],
    ['HU100', 9, 328, 'text'],
    ['INTPTLAT', 11, 337, 'text'],
    ['INTPTLON', 12, 348, 'text'],
    ['LSADC', 2, 360, 'text'],
    ['PARTFLAG', 1, 362, 'text'],
    ['RESERVE3', 6, 363, 'text'],
    ['UGA', 5, 369, 'text'],
    ['STATENS', 8, 374, 'text'],
    ['COUNTYNS', 8, 382, 'text'],
    ['COUSUBNS', 8, 390, 'text'],
    ['PLACENS', 8, 398, 'text'],
    ['CONCITNS', 8, 406, 'text'],
    ['AIANHHNS', 8, 414, 'text'],
    ['AITSNS', 8, 422, 'text'],
    ['ANRCNS', 8, 430, 'text'],
    ['SUBMCDNS', 8, 438, 'text'],
    ['CD113', 2, 446, 'text'],
    ['CD114', 2, 448, 'text'],
    ['CD115', 2, 450, 'text'],
    ['SLDU2', 3, 452, 'text'],
    ['SLDU3', 3, 455, 'text'],
    ['SLDU4', 3, 458, 'text'],
    ['SLDL2', 3, 461, 'text'],
    ['SLDL3', 3, 464, 'text'],
    ['SLDL4', 3, 467, 'text'],
    ['AIANHHSC', 2, 470, 'text'],
    ['CSASC', 2, 472, 'text'],
    ['CNECTASC', 2, 474, 'text'],
    ['MEMI', 1, 476, 'text'],
    ['NMEMI', 1, 477, 'text'],
    ['PUMA', 5, 478, 'text'],
    ['RESERVED', 18, 483, 'text'],
   ],
   acs_2009 =>
   [
     ['FILEID', 6, 1, 'text'],
     ['STUSAB', 2, 7, 'text'],
     ['SUMLEVEL', 3, 9, 'text'],
     ['COMPONENT', 2, 12, 'text'],
     ['LOGRECNO', 7, 14, 'text'],
     ['US', 1, 21, 'text'],
     ['REGION', 1, 22, 'text'],
     ['DIVISION', 1, 23, 'text'],
     ['STATECE', 2, 24, 'text'],
     ['STATE', 2, 26, 'text'],
     ['COUNTY', 3, 28, 'text'],
     ['COUSUB', 5, 31, 'text'],
     ['PLACE', 5, 36, 'text'],
     ['BLANK1', 6, 41, 'text'],
     ['BLANK2', 1, 47, 'text'],
     ['BLANK3', 5, 48, 'text'],
     ['AIANHH', 4, 53, 'text'],
     ['AIANHHFP', 5, 57, 'text'],
     ['BLANK4', 1, 62, 'text'],
     ['BLANK5', 3, 63, 'text'],
     ['BLANK6', 5, 66, 'text'],
     ['ANRC', 5, 71, 'text'],
     ['CBSA', 5, 76, 'text'],
     ['CSA', 3, 81, 'text'],
     ['METDIV', 5, 84, 'text'],
     ['MACC', 1, 89, 'text'],
     ['MEMI', 1, 90, 'text'],
     ['NECTA', 5, 91, 'text'],
     ['CNECTA', 3, 96, 'text'],
     ['NECTADIV', 5, 99, 'text'],
     ['UA', 5, 104, 'text'],
     ['BLANK7', 5, 109, 'text'],
     ['CDCURR', 2, 114, 'text'],
     ['BLANK8', 3, 116, 'text'],
     ['BLANK9', 3, 119, 'text'],
     ['BLANK10', 6, 122, 'text'],
     ['BLANK11', 3, 128, 'text'],
     ['BLANK12', 5, 131, 'text'],
     ['SUBMCD', 5, 136, 'text'],
     ['SDELM', 5, 141, 'text'],
     ['SDSEC', 5, 146, 'text'],
     ['SDUNI', 5, 151, 'text'],
     ['UR', 1, 156, 'text'],
     ['PCI', 1, 157, 'text'],
     ['BLANK13', 6, 158, 'text'],
     ['BLANK14', 5, 164, 'text'],
     ['PUMA5', 5, 169, 'text'],
     ['BLANK15', 5, 174, 'text'],
     ['GEOID', 40, 179, 'text'],
     ['NAME', 200, 219, 'text'],
   ],
   acs_2010 =>
   [
    ['FILEID', 6, 1, 'text'],
    ['STUSAB', 2, 7, 'text'],
    ['SUMLEVEL', 3, 9, 'text'],
    ['COMPONENT', 2, 12, 'text'],
    ['LOGRECNO', 7, 14, 'text'],
    ['US', 1, 21, 'text'],
    ['REGION', 1, 22, 'text'],
    ['DIVISION', 1, 23, 'text'],
    ['STATECE', 2, 24, 'text'],
    ['STATE', 2, 26, 'text'],
    ['COUNTY', 3, 28, 'text'],
    ['COUSUB', 5, 31, 'text'],
    ['PLACE', 5, 36, 'text'],
    ['TRACT', 6, 41, 'text'],
    ['BLKGRP', 1, 47, 'text'],
    ['CONCIT', 5, 48, 'text'],
    ['AIANHH', 4, 53, 'text'],
    ['AIANHHFP', 5, 57, 'text'],
    ['AIHHTLI', 1, 62, 'text'],
    ['AITSCE', 3, 63, 'text'],
    ['AITS', 5, 66, 'text'],
    ['ANRC', 5, 71, 'text'],
    ['CBSA', 5, 76, 'text'],
    ['CSA', 3, 81, 'text'],
    ['METDIV', 5, 84, 'text'],
    ['MACC', 1, 89, 'text'],
    ['MEMI', 1, 90, 'text'],
    ['NECTA', 5, 91, 'text'],
    ['CNECTA', 3, 96, 'text'],
    ['NECTADIV', 5, 99, 'text'],
    ['UA', 5, 104, 'text'],
    ['BLANK1', 5, 109, 'text'],
    ['CDCURR', 2, 114, 'text'],
    ['SLDU', 3, 116, 'text'],
    ['SLDL', 3, 119, 'text'],
    ['BLANK2', 6, 122, 'text'],
    ['BLANK3', 3, 128, 'text'],
    ['BLANK4', 5, 131, 'text'],
    ['SUBMCD', 5, 136, 'text'],
    ['SDELM', 5, 141, 'text'],
    ['SDSEC', 5, 146, 'text'],
    ['SDUNI', 5, 151, 'text'],
    ['UR', 1, 156, 'text'],
    ['PCI', 1, 157, 'text'],
    ['BLANK5', 6, 158, 'text'],
    ['BLANK6', 5, 164, 'text'],
    ['PUMA5', 5, 169, 'text'],
    ['BLANK', 5, 174, 'text'],
    ['GEOID', 40, 179, 'text'],
    ['NAME', 200, 219, 'text'],
    ['BTTR', 6, 419, 'text'],
    ['BTBG', 1, 425, 'text'],
    ['BLANK7', 50, 426, 'text'],
   ],
   acs_2011 =>
   [
    ['FILEID', 6, 1, 'text'],
    ['STUSAB', 2, 7, 'text'],
    ['SUMLEVEL', 3, 9, 'text'],
    ['COMPONENT', 2, 12, 'text'],
    ['LOGRECNO', 7, 14, 'text'],
    ['US', 1, 21, 'text'],
    ['REGION', 1, 22, 'text'],
    ['DIVISION', 1, 23, 'text'],
    ['STATECE', 2, 24, 'text'],
    ['STATE', 2, 26, 'text'],
    ['COUNTY', 3, 28, 'text'],
    ['COUSUB', 5, 31, 'text'],
    ['PLACE', 5, 36, 'text'],
    ['TRACT', 6, 41, 'text'],
    ['BLKGRP', 1, 47, 'text'],
    ['CONCIT', 5, 48, 'text'],
    ['AIANHH', 4, 53, 'text'],
    ['AIANHHFP', 5, 57, 'text'],
    ['AIHHTLI', 1, 62, 'text'],
    ['AITSCE', 3, 63, 'text'],
    ['AITS', 5, 66, 'text'],
    ['ANRC', 5, 71, 'text'],
    ['CBSA', 5, 76, 'text'],
    ['CSA', 3, 81, 'text'],
    ['METDIV', 5, 84, 'text'],
    ['MACC', 1, 89, 'text'],
    ['MEMI', 1, 90, 'text'],
    ['NECTA', 5, 91, 'text'],
    ['CNECTA', 3, 96, 'text'],
    ['NECTADIV', 5, 99, 'text'],
    ['UA', 5, 104, 'text'],
    ['BLANK1', 5, 109, 'text'],
    ['CDCURR', 2, 114, 'text'],
    ['SLDU', 3, 116, 'text'],
    ['SLDL', 3, 119, 'text'],
    ['BLANK2', 6, 122, 'text'],
    ['BLANK3', 3, 128, 'text'],
    ['ZCTA5', 5, 131, 'text'],
    ['SUBMCD', 5, 136, 'text'],
    ['SDELM', 5, 141, 'text'],
    ['SDSEC', 5, 146, 'text'],
    ['SDUNI', 5, 151, 'text'],
    ['UR', 1, 156, 'text'],
    ['PCI', 1, 157, 'text'],
    ['BLANK4', 6, 158, 'text'],
    ['BLANK5', 5, 164, 'text'],
    ['PUMA5', 5, 169, 'text'],
    ['BLANK6', 5, 174, 'text'],
    ['GEOID', 40, 179, 'text'],
    ['NAME', 1000, 219, 'text'],
    ['BTTR', 6, 1219, 'text'],
    ['BTBG', 1, 1225, 'text'],
    ['BLANK7', 44, 1226, 'text'],
   ],
   acs_2012 =>
   [
    ['FILEID', 6, 1, 'text'],
    ['STUSAB', 2, 7, 'text'],
    ['SUMLEVEL', 3, 9, 'text'],
    ['COMPONENT', 2, 12, 'text'],
    ['LOGRECNO', 7, 14, 'text'],
    ['US', 1, 21, 'text'],
    ['REGION', 1, 22, 'text'],
    ['DIVISION', 1, 23, 'text'],
    ['STATECE', 2, 24, 'text'],
    ['STATE', 2, 26, 'text'],
    ['COUNTY', 3, 28, 'text'],
    ['COUSUB', 5, 31, 'text'],
    ['PLACE', 5, 36, 'text'],
    ['TRACT', 6, 41, 'text'],
    ['BLKGRP', 1, 47, 'text'],
    ['CONCIT', 5, 48, 'text'],
    ['AIANHH', 4, 53, 'text'],
    ['AIANHHFP', 5, 57, 'text'],
    ['AIHHTLI', 1, 62, 'text'],
    ['AITSCE', 3, 63, 'text'],
    ['AITS', 5, 66, 'text'],
    ['ANRC', 5, 71, 'text'],
    ['CBSA', 5, 76, 'text'],
    ['CSA', 3, 81, 'text'],
    ['METDIV', 5, 84, 'text'],
    ['MACC', 1, 89, 'text'],
    ['MEMI', 1, 90, 'text'],
    ['NECTA', 5, 91, 'text'],
    ['CNECTA', 3, 96, 'text'],
    ['NECTADIV', 5, 99, 'text'],
    ['UA', 5, 104, 'text'],
    ['BLANK1', 5, 109, 'text'],
    ['CDCURR', 2, 114, 'text'],
    ['SLDU', 3, 116, 'text'],
    ['SLDL', 3, 119, 'text'],
    ['BLANK2', 6, 122, 'text'],
    ['BLANK3', 3, 128, 'text'],
    ['ZCTA5', 5, 131, 'text'],
    ['SUBMCD', 5, 136, 'text'],
    ['SDELM', 5, 141, 'text'],
    ['SDSEC', 5, 146, 'text'],
    ['SDUNI', 5, 151, 'text'],
    ['UR', 1, 156, 'text'],
    ['PCI', 1, 157, 'text'],
    ['BLANK4', 6, 158, 'text'],
    ['BLANK5', 5, 164, 'text'],
    ['PUMA5', 5, 169, 'text'],
    ['BLANK6', 5, 174, 'text'],
    ['GEOID', 40, 179, 'text'],
    ['NAME', 1000, 219, 'text'],
    ['BTTR', 6, 1219, 'text'],
    ['BTBG', 1, 1225, 'text'],
    ['BLANK7', 44, 1226, 'text'],
   ],
  );

sub fixed_to_sqlite{
  my ($file, $table_name, $db_file, $aref) = @_;
  if (-f $db_file){
    unlink ($db_file) or croak "Could not delete $db_file";
  }
  if (-f "$db_file.part"){
    unlink ("$db_file.part") or croak "Could not delete $db_file.part";
  }
  my $dref = DBI->connect("dbi:SQLite:dbname=$db_file.part", "", "") or croak DBI->errstr;
  my $string = "create table $table_name (" . join(", ", map {$_->[0] . " " . $_->[3]} @{$aref}) . ")";
  print STDERR "String is $string\n";
  $dref->do($string) or croak $dref->errstr;
  $string = "insert into $table_name (" . join(", ", map {$_->[0]} @{$aref}) . ") values (" . join(", ", map {'?'} @{$aref}) . ")";
  my $statement = $dref->prepare($string) or croak $dref->errstr;
  my $fh = IO::File->new("< $file") or croak "Could not read the file $file";
  $dref->begin_work();
  my $count = 0;
  while (my $line = <$fh>){
    if ($count++ > 2000){
      $dref->commit();
      $dref->begin_work();
      $count = 0;
    }
    $statement->execute(map {mytrim(substr($line, $_->[2] - 1 , $_->[1]))} @{$aref}) or croak $statement->errstr;
  }
  $dref->commit();
  $dref->disconnect();
  $fh->close();
  move("$db_file.part", $db_file) or croak "Could not move $db_file into place";
  return;
}

sub mytrim{
  my $string = shift;
  $string =~ s/^ +| +$//g;
  $string = undef if ($string eq "");
  return($string);
}

my %decode_field =
  (
   census_2000 => sub{
     my $field = shift;
     my %result;
     if ($field =~ /([A-Z]+)([0-9]{3})([0-9]{3})/){
       $result{table} = "$1$2";
       $result{char} = $1;
       $result{one} = $2;
       $result{two} = $3;
     }
     elsif ($field =~ /([A-Z]+)([0-9]{3})([A-Z]+)([0-9]{3})/){
       $result{table} = $1 . $2 . $3;
       $result{char} = $1;
       $result{one} = $2;
       $result{chartwo} = $3;
       $result{two} = $4;
     }
     else{
       croak "Bad format for field $field";
     }
     $result{code} = $field;
     return(\%result);
   },
   census_2010 => sub{
     my $field = shift;
     my %result;
     if ($field =~ /([A-Z]+)([0-9]{3})([0-9]{4})/){
       $result{table} = sprintf('%s%d', $1, $2);
       $result{char} = $1;
       $result{one} = $2;
       $result{two} = $3;
     }
     elsif ($field =~ /([A-Z]+)([0-9]{3})([A-Z]+)([0-9]{3})/){
       $result{table} = sprintf('%s%d%s', $1, $2, $3);
       $result{char} = $1;
       $result{one} = $2;
       $result{chartwo} = $3;
       $result{two} = $4;
     }
     else{
       croak "Bad format for field $field";
     }
     $result{code} = $field;
     return(\%result);
   },
   acs => sub{
     my $field = shift;
     my %result;
     if ($field =~ /([A-Z])([0-9]{5})([A-Z]*)\_([0-9]+)/){
       $result{table} = "$1$2";
       $result{table} .= $3 if ($3);
       $result{char} = $1;
       $result{one} = $2;
       $result{chartwo} = $3;
       $result{two} = $4;
       $result{code} = $field;
     }
     elsif ($field =~ /([A-Z])([0-9]{5})([A-Z]*)/){
       $result{table} = "$1$2";
       $result{table} .= $3 if ($3);
       $result{char} = $1;
       $result{one} = $2;
       $result{chartwo} = $3;
       $result{two} = '001';
     }
     else{
       croak "Bad format for field $field";
     }
     $result{code} = sprintf('%s_%03d', $result{table}, $result{two});
     return(\%result);
   },
  );

my %fetch_table_file =
  (
   census_2010 => sub {
     my $self = shift;
     my %args = @_;
     my $data_filename = $data_file_of{$args{dataset}}->{$self->get_subset()}->(%args);
     my $data_file = File::Spec->catfile($args{directory}, $args{postal_code}, $data_filename);
     unless (-f $data_file){
       #print STDERR "Need to extract $data_filename\n";
       my $zip = Archive::Zip->new();
       croak "Could not read " . $args{state_file} unless ( $zip->read( $args{state_file} ) == AZ_OK );
       croak "Could not extract files" unless ( $zip->extractMember($data_filename, $data_file . '.part') == AZ_OK );
       move($data_file . '.part', $data_file) or croak "Could not move $data_file into place";
     }
     return($data_file);
   },
   census_2000 => sub {
     my $self = shift;
     my %args = @_;
     my $data_url = $data_url_of{$self->get_dataset()}->{$self->get_subset()}->(%args);
     my $data_filename = $data_file_of{$args{dataset}}->{$self->get_subset()}->(%args);
     my $data_file = File::Spec->catfile($args{directory}, $args{postal_code}, $data_filename);
     my $data_zip_file = $data_file . ".zip";
     if (-f $data_zip_file){
       unlink ($data_zip_file) or croak "Could not delete $data_zip_file";
     }
     my $ua = LWP::UserAgent->new();
     my $response = $ua->get($data_url, ':content_file' => $data_zip_file);
     croak $response->status_line unless ($response->is_success);
     if (-f $data_file){
       unlink ($data_file) or croak "Could not delete $data_file";
     }
     print STDERR "Need to extract $data_filename\n";
     my $zip = Archive::Zip->new();
     croak "Could not read $data_zip_file" unless ( $zip->read( $data_zip_file ) == AZ_OK );
     croak "Could not extract files" unless ( $zip->extractMember($data_filename, $data_file . '.part') == AZ_OK );
     unlink ($data_zip_file) or croak "Could not delete $data_zip_file";
     move($data_file . '.part', $data_file) or croak "Could not move $data_file into place";
     return($data_file);
   },
   acs => sub {
     my $self = shift;
     my %args = @_;
     my $data_url = $data_url_of{acs}->(%args);
     my $data_filename = $data_file_of{acs}->(%args);
     my $data_file = File::Spec->catfile($args{state_dir}, $data_filename);
     my $data_zip_file = $data_file . ".zip";
     if (-f $data_zip_file){
       unlink ($data_zip_file) or croak "Could not delete $data_zip_file";
     }
     print STDERR "Fetching $data_url for $args{segment}\n";
     my $ua = LWP::UserAgent->new();
     my $response = $ua->get($data_url, ':content_file' => $data_zip_file);
     croak $response->status_line unless ($response->is_success);
     if (-f $data_file){
       unlink ($data_file) or croak "Could not delete $data_file";
     }
     if (-f "$data_file.m"){
       unlink ("$data_file.e") or croak "Could not delete $data_file.e";
     }
     if (-f "$data_file.m"){
       unlink ("$data_file.m") or croak "Could not delete $data_file.m";
     }
     print STDERR "Need to extract $data_filename\n";
     my $zip = Archive::Zip->new();
     croak "Could not read $data_zip_file" unless ( $zip->read( $data_zip_file ) == AZ_OK );
     croak "Could not extract files" unless ( $zip->extractMember('e' . $data_filename, "$data_file.e") == AZ_OK );
     croak "Could not extract files" unless ( $zip->extractMember('m' . $data_filename, "$data_file.m") == AZ_OK );
     unlink ($data_zip_file) or croak "Could not delete $data_zip_file";
     my $outfh = IO::File->new("> $data_file") or croak "Could not open $data_file";
     foreach my $file ("$data_file.e", "$data_file.m"){
       my $infh = IO::File->new($file) or croak "Could not read file";
       while (my $line = <$infh>){
	 print $outfh $line;
       }
       $infh->close();
       unlink ($file) or croak "Could not delete $file";
     }
     $outfh->close();
     print STDERR "Data file is $data_file\n";
     return($data_file);
   },
  );

foreach my $key (keys %dataset_dispatch){
  next unless ($key =~ /^acs/);
  $fetch_table_file{$key} = $fetch_table_file{acs};
}

sub get_years_of{
  my $self = shift;
  my $dataset = $self->get_dataset();
  if ($dataset =~ /([1-9])yr$/){
    return($1);
  }
  return(0);
}

sub get_sumlevel{
  my $self = shift;
  my %args = @_;
  my $sumlevel;
  unless ($args{sumlevel}){
    if ($args{level}){
      return($self->get_sum_level_of($args{level}));
    }
  }
  return($args{sumlevel});
}

sub get_data_file {
  my $self = shift;
  my %args = @_;
  $args{postalcode} = $self->get_postalcode(%args);
  croak "No postalcode provided" unless ($args{postalcode});
  my @out;
  my $state_dir;
  push (@out, $self->get_directory());
  push (@out, $self->get_dataset());
  if ($data_file_of{$self->get_dataset()}){
    push(@out, $self->get_subset());
  }
  push(@out, $args{postalcode});
  my $sumlevel = $self->get_sumlevel(%args);
  if ($self->get_years_of() == 5){
    croak "Level not supplied 2" unless ($sumlevel);
    if ($sumlevel eq "140" || $sumlevel eq "150"){
      $state_dir .= "tracts_block_groups_only";
    }
    else{
      $state_dir .= "all_geographies";
    }
    push(@out, $state_dir);
  }
  my $file = File::Spec->catfile(@out, "data.sqlite");
  #warn "Sumlevel is $sumlevel.  Checking for existence of $file";
  return((-f $file) ? $file : undef);
}

sub get_lookup_file {
  my $self = shift;
  my @out;
  push (@out, $self->get_directory());
  push (@out, $self->get_dataset());
  if ($data_file_of{$self->get_dataset()}){
    push(@out, $self->get_subset());
  }
  my $file = File::Spec->catfile(@out, "lookup.sqlite");
  return((-f $file) ? $file : undef);
}

sub fetch_census_2000{
  my $self = shift;
  my %args = @_;
  $args{endyear} = 2000;
  croak "No data url for dataset " . $self->get_dataset() unless ($data_url_of{$self->get_dataset()});
  croak "Need to specify set to be one of: " . join(", ", keys %{$data_url_of{$self->get_dataset()}}) unless ($self->get_subset() && $data_url_of{$self->get_dataset()}->{$self->get_subset()});
  croak "Need to specify set to be one of: " . join(", ", keys %{$geo_url_of{census_2000}->{$self->get_subset()}}) unless ($self->get_subset() && $geo_url_of{census_2000}->{$self->get_subset()});
  #$args{data_url} = $data_url_of{census_2000}->{$self->get_subset()}->(%args);
  $args{directory} = File::Spec->catfile($args{directory}, $self->get_subset());
  unless (-d $args{directory}){
    mkdir($args{directory}) or croak "1445: Could not create directory $args{directory}";
  }
  my @postal_code_dirs = ($args{directory}, $args{postal_code});
  my $postal_code_directory = File::Spec->catdir();
  unless (-d $postal_code_directory){
    mkdir($postal_code_directory) or croak "1450: Could not create directory $postal_code_directory";
  }
  my $data_db_file = File::Spec->catfile(@postal_code_dirs, "data.sqlite");
  unless (-f $data_db_file){
    my $geo_file = File::Spec->catfile(@postal_code_dirs, "geo.txt");
    my $geo_zip_file = File::Spec->catfile(@postal_code_dirs, "geo.zip");
    if (-f $geo_file){
      unlink ($geo_file) or croak "Could not delete $geo_file";
    }
    if (-f $geo_zip_file){
      unlink ($geo_zip_file) or croak "Could not delete $geo_zip_file";
    }
    my $ua = LWP::UserAgent->new();
    my ($geo_url, $geo_filename) = $geo_url_of{census_2000}->{$self->get_subset()}->(%args);
    my $response = $ua->get($geo_url, ':content_file' => $geo_zip_file . '.part');
    croak $response->status_line unless ($response->is_success);
    move($geo_zip_file . '.part', $geo_zip_file) or croak "Could not move $geo_file into place";
    my $zip = Archive::Zip->new();
    croak "Could not read geo file $geo_file" unless ( $zip->read( $geo_zip_file ) == AZ_OK );
    croak "Could not extract files" unless ( $zip->extractMember($geo_filename, $geo_file . '.part') == AZ_OK );
    move($geo_file . '.part', $geo_file) or croak "Could not move $geo_file into place";
    fixed_to_sqlite($geo_file, 'geo', $data_db_file, $geo_cols{census_2000});
    my $dref = DBI->connect("dbi:SQLite:dbname=$data_db_file", "", "") or croak DBI->errstr;
    if ($args{dataset} =~ /^acs/){
      $dref->do("create index indexgeosumlev on geo (SUMLEVEL, LOGRECNO, COMPONENT, COUNTY)");
    }
    else{
      $dref->do("create index indexgeosumlev on geo (SUMLEV, LOGRECNO, GEOCOMP, COUNTY)");
    }
    $dref->disconnect();
    if (-f $geo_zip_file){
      unlink ($geo_zip_file) or croak "Could not delete $geo_zip_file";
    }
    #if (-f $geo_file){
    #  unlink ($geo_file) or croak "Could not delete $geo_file";
    #}
  }
  my $lookup_db_file = File::Spec->catfile($args{directory}, "lookup.sqlite");
  unless (-f $lookup_db_file){
    my $lookup_file;
    {
      my $this_path = $INC{File::Spec->catfile("Census", "US.pm")};
      croak "Could not find path" unless ($this_path);
      my $perl_path = dirname($this_path);
      $lookup_file = File::Spec->catfile($perl_path, "US", $lookup_file_of{$self->get_dataset()}->{$self->get_subset()});
      #print STDERR "Lookup file is $lookup_file\n";
    }
    get_decennial_lookup($lookup_file, $lookup_db_file);
  }
  return($self->fetch_fields(%args, lookup_db_file => $lookup_db_file, data_db_file => $data_db_file));
}

sub fetch_census_2010{
  my $self = shift;
  my %args = @_;
  $args{endyear} = 2010;
  croak "No data url for dataset " . $self->get_dataset() unless ($data_url_of{$self->get_dataset()});
  croak "Need to specify set to be one of: " . join(", ", keys %{$data_url_of{$self->get_dataset()}}) unless ($self->get_subset() && $data_url_of{$self->get_dataset()}->{$self->get_subset()});
  $args{directory} = File::Spec->catfile($args{directory}, $self->get_subset());
  unless (-d $args{directory}){
    mkdir($args{directory}) or croak "1510: Could not create directory $args{directory}";
  }
  my @postal_code_dirs = ($args{directory}, $args{postal_code});
  my $postal_code_directory = File::Spec->catdir(@postal_code_dirs);
  unless (-d $postal_code_directory){
    mkdir($postal_code_directory) or croak "1515: Could not create directory $postal_code_directory";
  }
  my ($data_zip_url, $geo_filename) = $data_url_of{census_2010}->{$self->get_subset()}->(%args);
  my $state_file = File::Spec->catfile(@postal_code_dirs, "state_file.zip");
  $args{state_file} = $state_file;
  unless (-f $state_file){
    my $ua = LWP::UserAgent->new();
    my $response = $ua->get($data_zip_url, ':content_file' => $state_file . '.part');
    croak $response->status_line unless ($response->is_success);
    move($state_file . '.part', $state_file) or croak "Could not move $state_file into place";
  }
  my $data_db_file = File::Spec->catfile(@postal_code_dirs, "data.sqlite");
  unless (-f $data_db_file){
    my $geo_file = File::Spec->catfile(@postal_code_dirs, "geo.txt");
    my $zip = Archive::Zip->new();
    croak "Could not read state file $state_file" unless ( $zip->read( $state_file ) == AZ_OK );
    croak "Could not extract files" unless ( $zip->extractMember($geo_filename, $geo_file . '.part') == AZ_OK );
    move($geo_file . '.part', $geo_file) or croak "Could not move $geo_file into place";
    fixed_to_sqlite($geo_file, 'geo', $data_db_file, $geo_cols{census_2010});
    my $dref = DBI->connect("dbi:SQLite:dbname=$data_db_file", "", "") or croak DBI->errstr;
    $dref->do("create index indexgeosumlev on geo (SUMLEV, COUNTY)");
    $dref->disconnect();
    if (-f $geo_file){
      unlink ($geo_file) or croak "Could not delete $geo_file";
    }
  }
  my $lookup_db_file = File::Spec->catfile($args{directory}, "lookup.sqlite");
  unless (-f $lookup_db_file){
    my $lookup_file;
    {
      my $this_path = $INC{File::Spec->catfile("Census", "US.pm")};
      croak "Could not find path" unless ($this_path);
      my $perl_path = dirname($this_path);
      $lookup_file = File::Spec->catfile($perl_path, 'US', $lookup_file_of{$self->get_dataset()}->{$self->get_subset()});
      #print STDERR "Lookup file is $lookup_file\n";
    }
    get_decennial_lookup($lookup_file, $lookup_db_file);
  }
  return($self->fetch_fields(%args, lookup_db_file => $lookup_db_file, data_db_file => $data_db_file));
}

sub fetch_fields{
  my $self = shift;
  my %args = @_;
  my $lookup_db_file = $args{lookup_db_file};
  #warn "Lookup db is $args{lookup_db_file}";
  my $data_db_file = $args{data_db_file};
  my $result = $args{result} // {};
  if ($args{field}){
    my @fields;
    my %fieldtrans;
    if (ref($args{field})){
      if (ref($args{field}) eq "HASH"){
	while (my ($key, $data) = each %{$args{field}}){
	  push(@fields, $data);
	  $fieldtrans{$data} = $key;
	}
      }
      else{
	croak "Invalid field" unless (ref($args{field}) eq "ARRAY");
	@fields = @{$args{field}};
      }
    }
    else{
      push(@fields, $args{field});
    }
    foreach my $field (@fields){
      print STDERR "Processing field $field\n";
      my ($segment, $col, $universe, $subuniverse);
      my %tables;
      {
	my $dref = DBI->connect("dbi:SQLite:dbname=$data_db_file", "", "") or croak DBI->errstr;
	{
	  my $query = $dref->table_info() or croak $dref->errstr;
	  while (my $d = $query->fetchrow_hashref()){
	    $tables{$d->{TABLE_NAME}} = undef if ($d->{TABLE_NAME});
	  }
	}
	$dref->disconnect();
      }
      {
	my $dref = DBI->connect("dbi:SQLite:dbname=$lookup_db_file", "", "") or croak DBI->errstr;
	my $order = ($args{dataset} =~ /acs/) ? " order by sequence" : "";
	my $query = $dref->prepare("select * from lookup where tableid=?$order") or croak $dref->errstr;
	my $fields;
	if ($decode_field{$self->get_dataset()}){
	  $fields = $decode_field{$self->get_dataset()}->($field);
	}
	else{
	  my $name = $self->get_dataset();
	  $name =~ s/[^a-z].*//;
	  $fields = $decode_field{$name}->($field);
	}
	print STDERR "Table ID is $fields->{table}\n";
	$query->execute($fields->{table}) or croak $query->errstr;
	while (my $d = $query->fetchrow_hashref()){
	  print STDERR "Found $d->{definition}\n";
	  $universe //= $d->{universe};
	  my $a;
	  eval '$a = ' . $d->{definition} . ';';
	  croak "Could not read array reference for $fields->{table}" unless ($a);
	  foreach my $item (@{$a}){
	    if ($item->[1] =~ /^(.*):$/){
	      my $name = $1;
	      if ($item->[0] eq $field){
		$subuniverse = undef;
	      }
	      else{
		$subuniverse = $name;
	      }
	    }
	    if ($item->[0] eq $fields->{code}){
	      ($segment, $col) = ($item->[2], $item->[3]);
	      last;
	    }
	  }
	  last;
	}
	$query->finish();
	$dref->disconnect();
      }
      croak "No segment found" unless ($segment);
      #print STDERR "Using $segment, $universe, $subuniverse\n";
      my $dref = DBI->connect("dbi:SQLite:dbname=$data_db_file", "", "") or croak DBI->errstr;
      my %geo_columns;
      {
	my $statement = $dref->prepare("select * from geo limit 1") or croak $dref->errstr;
	$statement->execute() or croak $statement->errstr;
	%geo_columns = map {$_ => 1} keys %{$statement->fetchrow_hashref()};
	$statement->finish();
      }
      my $table = sprintf('seg%04d%03d', $segment, $args{iteration} // 0);
      my $geo_col = sprintf('c%03d', ($args{geo_col} // 4));
      my $target_col = sprintf('c%03d', ($args{base_col} // 5) + $col);
      unless (exists($tables{$table})){
	croak "Cannot fetch table" unless ($fetch_table_file{$self->get_dataset()});
	my $data_file = $fetch_table_file{$self->get_dataset()}->($self, %args, segment => $segment);
	my $csv = Text::CSV_XS->new
	  ({
	    binary => 1,
	    sep_char => ',',
	    allow_whitespace => 1,
	    blank_is_undef => 0,
	    empty_is_undef => 0,
	   }) or die "Cannot use CSV: " . Text::CSV_XS->error_diag();
	my $fh = IO::File->new("< $data_file") or croak "Could not load $data_file";
	my $row = $csv->getline($fh);
	croak "Could not read data file $data_file" unless ($row && ref($row) eq "ARRAY");
	my $num_columns = scalar(@{$row});
	$dref->do("drop table if exists part$table") or croak $dref->errstr;
	$dref->do("create table part$table (" . join(", ", map {sprintf('c%03d text', $_)} (0 .. ($num_columns - 1))) . ")") or croak $dref->errstr;
	my $statement = $dref->prepare("insert into part$table (" . join(", ", map {sprintf('c%03d', $_)} (0 .. ($num_columns - 1))) . ") values (" . join(", ", map {'?'} (0 .. ($num_columns - 1))) . ")") or croak $dref->errstr;
	$fh->seek(0, 0);
	my $count = 0;
	$dref->begin_work();
	while (my $row = $csv->getline($fh)){
	  if ($count++ > 1000){
	    $dref->commit();
	    $dref->begin_work();
	    $count = 0;
	  }
	  $statement->execute(@{$row}) or croak $statement->errstr;
	}
	$dref->commit();
	$dref->do("drop table if exists $table") or croak $dref->errstr;
	$dref->do("alter table part$table rename to $table") or croak $dref->errstr;
	$dref->do("create index index$table on $table ($geo_col)") or croak $dref->errstr;
	print STDERR "Created index\n";
	$fh->close();
	unlink($data_file) or croak "Could not remove data file $data_file";
      }
      my @geo = @{$cols_for_level{$args{level}} // $cols_for_level{$sum_level_key{$args{level}}}};
      foreach my $colname (@geo, "NAME"){
	croak "Could not load data for Summary Level " . ($sum_level_names{$args{level}} // $args{level}) . " from the selected dataset because column $colname could not be found in the Census data.  You may want to try a different data set." unless ($geo_columns{$colname});
      }
      my $limits = '';
      if ($args{limits}){
	croak "invalid limits" unless (ref($args{limits}) && ref($args{limits}) eq "HASH");
	my @all;
	while (my ($lim_col, $href) = each %{$args{limits}}){
	  my @list;
	  foreach my $value (keys %{$href}){
	    push (@list, "$lim_col like '$value'");
	  }
	  push(@all, "(" . join(" or ", @list) . ")");
	}
	$limits = " and " . join(" and ", @all) if (scalar(@all));
      }
      my $num_fetched = 0;
      if ($args{dataset} =~ /^acs/){
	my %typetrans = (
			 $args{endyear} . 'e' . $args{years} => "estimate",
			 $args{endyear} . 'm' . $args{years} => "margin",
			);
	my $string = "select a.NAME, b.c001, b.$target_col, " . join(", ", map {"a.$_"} @geo) . " from geo as a inner join $table as b on (a.LOGRECNO=b.$geo_col) where a.COMPONENT='00' and a.SUMLEVEL=?" . $limits;
	print STDERR "sum level is $args{sumlevel} and query is " . $string . "\n";
	my $query = $dref->prepare($string) or croak $dref->errstr;
	$query->execute($args{sumlevel}) or croak $query->errstr;
	while (my $d = $query->fetchrow_hashref()){
	  $d->{$target_col} = undef if ($d->{$target_col} && $d->{$target_col} eq '.');
	  my $type = $typetrans{$d->{c001}};
	  my $fips = $args{sumlevel} . '00US' . join('', map {$d->{$_} // 'ERROR'} @geo);
	  if ($type eq "estimate"){
	    $result->{$fips}->{$fieldtrans{$field} // $field} = $d->{$target_col};
	  }
	  else{
	    $result->{$fips}->{($fieldtrans{$field} // $field) . '-margin'} = $d->{$target_col};
	  }
	  $result->{$fips}->{geo_name} = $d->{NAME};
	  $num_fetched++;
	}
      }
      else{
	my $string = "select a.NAME, b.$target_col, " . join(", ", map {"a.$_"} @geo) . " from geo as a inner join $table as b on (a.LOGRECNO=b.$geo_col) where a.GEOCOMP='00' and a.SUMLEV=?" . $limits;
	print STDERR "sum level is $args{sumlevel} and query is " . $string . "\n";
	my $query = $dref->prepare($string) or croak $dref->errstr;
	$query->execute($args{sumlevel}) or croak $query->errstr;
	while (my $d = $query->fetchrow_hashref()){
	  $d->{$target_col} = undef if ($d->{$target_col} && $d->{$target_col} eq '.');
	  my $fips = $args{sumlevel} . '00US' . join('', map {$d->{$_} // 'ERROR'} @geo);
	  #print "Answer for county $d->{NAME} is " . $d->{$target_col} . "\n";
	  $result->{$fips}->{$fieldtrans{$field} // $field} = $d->{$target_col};
	  $result->{$fips}->{geo_name} = $d->{NAME};
	  $num_fetched++;
	}
      }
      unless ($num_fetched){
	print STDERR "Warning: no results were available for your selection\n";
      }
      $dref->disconnect();
    }
  }
  foreach my $transform (@{$args{transform}}){
    while (my ($fips, $item) = each %{$result}){
      $transform->($item);
    }
  }
  return $result;
}

sub get_decennial_lookup{
  my ($lookup_file, $lookup_db_file) = @_;
  if (-f $lookup_db_file){
    unlink($lookup_db_file);
  }
  if (-f "$lookup_db_file.part"){
    unlink("$lookup_db_file.part");
  }
  my $dref = DBI->connect("dbi:SQLite:dbname=$lookup_db_file.part", "", "") or croak DBI->errstr;
  $dref->do("create table lookup (tableid text, tabletitle text, subjectarea text, universe text, definition text)") or croak $dref->errstr;
  my $statement = $dref->prepare("insert into lookup (tableid, tabletitle, universe, definition) values (?, ?, ?, ?)") or croak $dref->errstr;
  croak "Lookup file $lookup_file not found" unless (-f $lookup_file);
  local $Data::Dumper::Indent = 0;
  local $Data::Dumper::Terse  = 1;
  warn "Reading lookup file $lookup_file";
  my $fh = IO::File->new("< $lookup_file") or croak "Could not read lookup file $lookup_file";
  while (my $line = <$fh>){
    last if ($line =~ /^__END__/);
  }
  my $csv = Text::CSV_XS->new
    ({
      binary => 1,
      sep_char => ',',
      allow_whitespace => 1,
      blank_is_undef => 0,
      empty_is_undef => 0,
     }) or die "Cannot use CSV: " . Text::CSV_XS->error_diag();
  my %trans =
    (
     "TABLE" => "TABLE NUMBER",
     "FIELDNUM" => "FIELD CODE",
     "TEXT" => "FIELD NAME",
     "SEG" => "SEGMENT",
    );
  my (@header_labels, %c);
  {
    my $header = $csv->getline($fh);
    my $i = 0;
    foreach my $column (@{$header}){
      $c{$column} = $i;
      if ($trans{$column}){
	$c{$trans{$column}} = $i;
      }
      push(@header_labels, $column);
      $i++;
    }
  }
  #print STDERR "Headers are " . join(", ", @header_labels) . " and c is " . Dumper(\%c) . "\n";
  my $last_cell;
  my %table;
  $dref->begin_work();
  my $count = 0;
  my $cur_segment;
  my $which_no = 1;
  my $col_count;
  while (my $row = $csv->getline($fh)){
    if ($row->[$c{"SEGMENT"}] ne "" && (!defined($cur_segment) || $cur_segment != int($row->[$c{"SEGMENT"}]))){
      $col_count = 0;
      $cur_segment = int($row->[$c{"SEGMENT"}]);
    }
    unless ($row->[$c{"FIELD CODE"}]){
      if ($row->[$c{"FIELD NAME"}] =~ /Universe/i){
	$table{universe} = $row->[$c{"FIELD NAME"}];
      }
      elsif ($row->[$c{"FIELD NAME"}] =~ / *\-+ *$/){
	push(@{$table{definition}}, [$row->[$c{"FIELD NAME"}], undef, undef]);
      }
      elsif ($row->[$c{"FIELD NAME"}] =~ / \[([0-9]+)\]/){
	$last_cell = $1;
	$table{table_title} = $row->[$c{"FIELD NAME"}];
	$table{table_title} =~ s/ \[([0-9]+)\]//;
	$table{table_id} = $row->[$c{"TABLE NUMBER"}]
      }
      elsif ($row->[$c{"FIELD NAME"}] eq ""){
	next;
      }
      else{
	croak "Could not read field name " . $row->[$c{"FIELD NAME"}];
      }
    }
    else{
      push(@{$table{definition}}, [$row->[$c{"FIELD CODE"}], $row->[$c{"FIELD NAME"}], $cur_segment, $col_count++]);
      if ($which_no == $last_cell){
	$statement->execute($table{table_id}, $table{table_title}, $table{universe}, Dumper($table{definition})) or croak $statement->errstr;
	undef %table;
	$which_no = 1;
      }
      else{
	$which_no++;
      }
    }
    if ($count++ > 1000){
      $dref->commit();
      #warn "Commit";
      $dref->begin_work();
      $count = 0;
    }
  }
  $dref->commit();
  $dref->disconnect();
  move("$lookup_db_file.part", $lookup_db_file) or croak "Could not move $lookup_db_file into place";
  return;
}

my %translate_lookup_column_names =
  (
   "fileid"                      => "File ID",
   "seq"                         => "Sequence Number",
   "Line Number Decimal M Lines" => "Line Number",
   "position"                    => "Start Position",
   "cells"                       => "Total Cells in Table",
   "total"                       => "Total Cells in Sequence",
   "Long Table Title"            => "Table Title",
   "subject_area"                => "Subject Area",
  );

sub fetch_acs{
  my $self = shift;
  my %args = @_;
  my $lookup_db_file = "$args{directory}/lookup.sqlite";
  unless (-f $lookup_db_file){
    my $lookup_file = "$args{directory}/lookup.txt";
    if (-f $lookup_file){
      unlink($lookup_file);
    }
    unless (defined($args{lookup_url})){
      $args{lookup_url} = "http://www2.census.gov/" . $self->get_dataset() . "/summaryfile/Sequence_Number_and_Table_Number_Lookup.txt";
    }
    my $ua = LWP::UserAgent->new();
    warn "Getting url $args{lookup_url} and saving to $lookup_file";
    my $response = $ua->get($args{lookup_url}, ':content_file' => $lookup_file . '.part');
    croak $response->status_line unless ($response->is_success);
    move($lookup_file . '.part', $lookup_file) or croak "Could not move $lookup_file into place";
    if (-f "$lookup_db_file.part"){
      unlink("$lookup_db_file.part");
    }
    my $dref = DBI->connect("dbi:SQLite:dbname=$lookup_db_file.part", "", "") or croak DBI->errstr;
    $dref->do("create table lookup (tableid text, sequence integer, tabletitle text, subjectarea text, universe text, definition text)") or croak $dref->errstr;
    my $statement = $dref->prepare("insert into lookup (tableid, sequence, tabletitle, subjectarea, universe, definition) values (?, ?, ?, ?, ?, ?)") or croak $dref->errstr;
    my $delstatement = $dref->prepare("delete from lookup where tableid=?") or croak $dref->errstr;
    local $Data::Dumper::Indent = 0;
    local $Data::Dumper::Terse  = 1;
    my $fh = IO::File->new("< $lookup_file") or croak "Could not load lookup file";
    my $csv = Text::CSV_XS->new ({
				  binary => 1,
				  sep_char => ',',
				  allow_whitespace => 1,
				  blank_is_undef => 0,
				  empty_is_undef => 0,
				 }) or die "Cannot use CSV: " . Text::CSV_XS->error_diag();
    my (@header_labels, %c);
    {
      my $header = $csv->getline($fh);
      my $i = 0;
      foreach my $column (@{$header}){
	$column = $translate_lookup_column_names{$column} // $column;
	$c{$column} = $i++;
	push(@header_labels, $column);
      }
    }
    my $last_cell;
    my %table;
    $dref->begin_work();
    my $count = 0;
    my $old_table_id = '';
    my $linecount;
    while (my $row = $csv->getline($fh)){
      if ($count++ > 1000){
	$dref->commit();
	#warn "Commit";
	$dref->begin_work();
	$count = 0;
      }
      if ($row->[$c{"Total Cells in Table"}] && $row->[$c{"Total Cells in Table"}] ne '.'){
	$last_cell = $row->[$c{"Total Cells in Table"}];
	$last_cell =~ s/[^0-9]+//g;
	if ($old_table_id eq $row->[$c{"Table ID"}]){
	  $dref->commit();
	  $dref->begin_work();
	  $delstatement->execute($old_table_id) or croak $delstatement->errstr;
	  $dref->commit();
	  $dref->begin_work();
	}
	else{
	  undef %table;
	  $table{table_id} = $row->[$c{"Table ID"}];
	  $table{table_title} = $row->[$c{"Table Title"}];
	  $table{subject_area} = $row->[$c{"Subject Area"}];
	}
	$table{sequence_number} = $row->[$c{"Sequence Number"}];
	$table{start_position} = $row->[$c{"Start Position"}];
	$linecount = 0;
	#warn "hi $last_cell";
      }
      elsif ($row->[$c{"Line Number"}] && $row->[$c{"Line Number"}] ne '.'){
	$linecount++;
	push(@{$table{definition}}, [sprintf('%s_%03d', $table{table_id}, $row->[$c{"Line Number"}]), $row->[$c{"Table Title"}], int($row->[$c{"Sequence Number"}]), $table{start_position} - 1 + $linecount]);
	#warn "adding info for " . $row->[$c{"Line Number"}];
	if ($row->[$c{"Sequence Number"}] ne $table{sequence_number}){
	  croak "This won't work";
	}
	if ($linecount == $last_cell){
	  #warn "Adding row";
	  $statement->execute($table{table_id}, $table{sequence_number}, $table{table_title}, $table{subject_area}, $table{universe}, Dumper($table{definition})) or croak $statement->errstr;
	  #undef %table;
	  $old_table_id = $table{table_id};
	}
      }
      else {
	$table{universe} = $row->[$c{"Table Title"}];
	#warn "hello $table{universe}";
      }
    }
    $dref->commit();
    $dref->disconnect();
    $fh->close();
    unlink($lookup_file) or croak "Could not delete $lookup_file";
    move("$lookup_db_file.part", $lookup_db_file) or croak "Could not move $lookup_db_file into place";
  }

  #warn "Getting state $args{postal_code}";
  my @state_dirs = ($args{directory}, $args{postal_code});
  my $state_dir = File::Spec->catdir(@state_dirs);
  unless (-d $state_dir){
    mkdir($state_dir) or croak "Could not create state directory $state_dir";
  }
  $args{sumlevel} = $self->get_sumlevel(%args);
  if ($args{years} == 5){
    croak "Level not supplied 3" unless ($args{sumlevel});
    if ($args{sumlevel} eq "140" || $args{sumlevel} eq "150"){
      push(@state_dirs, "tracts_block_groups_only");
    }
    else{
      push(@state_dirs, "all_geographies");
    }
    $state_dir = File::Spec->catdir(@state_dirs);
    unless (-d $state_dir){
      mkdir($state_dir) or croak "Could not create state directory $state_dir";
    }
  }
  $args{state_dir} = $state_dir;
  my $data_db_file = File::Spec->catfile($state_dir, "data.sqlite");
  unless (-f $data_db_file){
    my $geo_file = File::Spec->catfile($state_dir, "geo.txt");
    if (-f "$geo_file.part"){
      unlink("$geo_file.part") or croak "Could not delete $geo_file.part";
    }
    if (-f "$data_db_file.part"){
      unlink("$data_db_file.part") or croak "Could not delete $geo_file.part";
    }
    if ($args{endyear} eq "2012"){
      $args{geo_format} = "txt";
    }
    $args{geo_format} //= "csv";
    $args{geo_url} //= $args{by_state_by_sequence_url}->(%args) . "g" . $args{endyear} . $args{years} . lc($args{postal_code}) . "." . $args{geo_format};
    if (-f $geo_file){
      unlink($geo_file) or croak "Could not delete $geo_file";
    }
    my $ua = LWP::UserAgent->new();
    print STDERR "Getting url $args{geo_url} and saving to $geo_file\n";
    my $response = $ua->get($args{geo_url}, ':content_file' => $geo_file . '.part');
    croak "Could not get geometry file for $args{postal_code} using $args{geo_url}: " . $response->status_line unless ($response->is_success);
    move($geo_file . '.part', $geo_file) or croak "Could not move $geo_file into place";
    my @geo_cols;
    my $geo_def_ref;
    @geo_cols = map {$_->[0]} @{$geo_cols{"acs_" . $args{endyear}}};
    if ($args{geo_format} eq "csv"){
      my $dref = DBI->connect("dbi:SQLite:dbname=$data_db_file.part", "", "") or croak DBI->errstr;
      my $string = "create table geo (" . join(", ", map {"$_ text"} @geo_cols) . ")";
      $dref->do($string) or croak $dref->errstr;
      $string = "insert into geo (" . join(", ", @geo_cols) . ") values (" . join(", ", map {"?"} @geo_cols) . ")";
      #print STDERR "$string\n";
      my $statement = $dref->prepare($string) or croak $dref->errstr;
      my $csv = Text::CSV_XS->new
	({
	  binary => 1,
	  sep_char => ',',
	  allow_whitespace => 1,
	  blank_is_undef => 0,
	  empty_is_undef => 0,
	 }) or die "Cannot use CSV: " . Text::CSV_XS->error_diag();
      my $fh = IO::File->new("< $geo_file") or croak "Could not load $geo_file";
      my $count = 0;
      $dref->begin_work();
      while (my $row = $csv->getline($fh)){
	if ($count++ > 1000){
	  $dref->commit();
	  #warn "Commit";
	  $dref->begin_work();
	  $count = 0;
	}
	$statement->execute(@{$row}) or croak $statement->errstr;
      }
      $fh->close();
      $dref->commit();
      $dref->disconnect();
      move("$data_db_file.part", $data_db_file) or croak "Could not move $data_db_file into place";
    }
    elsif ($args{geo_format} eq "txt"){
      fixed_to_sqlite($geo_file, 'geo', $data_db_file, $geo_cols{"acs_" . $args{endyear}});
    }
    unlink($geo_file) or croak "Could not delete $geo_file";
    print STDERR "done with geo file import\n";
    my $dref = DBI->connect("dbi:SQLite:dbname=$data_db_file", "", "") or croak DBI->errstr;
    $dref->do("create index indexgeosumlev on geo (SUMLEVEL, COUNTY)");
    $dref->disconnect();
    print STDERR "done with geo file indexing\n";
  }
  croak "Level not supplied 1" unless ($args{sumlevel});
  $args{geo_col} = 5;
  $args{base_col} = -1;
  print STDERR "Calling fetch_fields\n";
  return($self->fetch_fields(%args, lookup_db_file => $lookup_db_file, data_db_file => $data_db_file));
}

sub new {
  my $proto = shift;
  my $class = ref($proto) || $proto;
  my $self  = {};
  bless ($self, $class);
  my %args = @_;
  if ($args{directory}){
    $self->set_directory($args{directory});
  }
  else{
    $self->set_directory(glob($default_directory));
  }
  if ($args{dataset}){
    $self->set_dataset($args{dataset});
  }
  if ($args{subset}){
    $self->set_subset($args{subset});
  }
  return $self;
}

sub get_fips_county_list {
  my $self = shift;
  my %args = @_;
  my $url = "http://quickfacts.census.gov/qfd/download/FIPS_CountyName.txt";
  my $fips_state = $fips_from_postal_code{get_postal_code_from_state($args{state})};
  croak "Invalid state $args{state}" unless ($fips_state);
  my $directory = $self->get_directory();
  unless (-d $directory){
    croak "Directory not available";
  }
  my $county_fips_file = File::Spec->catfile($directory, "county_fips.txt");
  unless (-f $county_fips_file){
    print STDERR "Getting URL $url\n";
    my $ua = LWP::UserAgent->new();
    my $response = $ua->get($url, ':content_file' => $county_fips_file);
    croak $response->status_line unless ($response->is_success);
  }
  my @list;
  {
    my $fp = IO::File->new("< $county_fips_file") or croak "Could not load file";
    while (my $line = <$fp>){
      next unless (substr($line, 0, 2) eq $fips_state);
      chomp $line;
      if ($line =~ /([0-9]{5}) (.*)/){
	push(@list, ['05000US' . $1, $2]);
      }
    }
    $fp->close();
  }
  #warn "returning list";
  return(\@list);
}

sub get_county_list {
  my $self = shift;
  my %args = @_;
  my $fips_state = $fips_from_postal_code{get_postal_code_from_state($args{state})};
  croak "Invalid state $args{state}" unless ($fips_state);
  my $directory = $self->get_directory();
  unless (-d $directory){
    croak "Directory not available";
  }
  my $county_fips_file = File::Spec->catfile($directory, "county_fips.txt");
  unless (-f $county_fips_file){
    my $url = "http://quickfacts.census.gov/qfd/download/FIPS_CountyName.txt";
    print STDERR "Getting URL $url\n";
    my $ua = LWP::UserAgent->new();
    my $response = $ua->get($url, ':content_file' => $county_fips_file);
    croak $response->status_line unless ($response->is_success);
  }
  my @list;
  {
    my $fp = IO::File->new("< $county_fips_file") or croak "Could not load file";
    while (my $line = <$fp>){
      next unless (substr($line, 0, 2) eq $fips_state);
      chomp $line;
      if ($line =~ /([0-9]{2})([0-9]{3}) (.*)/){
	push(@list, [$2, '05000US' . $1 . $2, $3]);
      }
    }
    $fp->close();
  }
  #warn "returning list";
  return(\@list);
}

sub fetch {
  my $self = shift;
  my %args = @_;
  croak $self->get_dataset() . " is not one of the data sets currently available through Census::US" unless ($dataset_dispatch{$self->get_dataset()});
  my $directory = $self->get_directory();
  unless (-d $directory){
    croak "Directory not available";
  }
  $args{dataset} = $self->get_dataset();
  $args{subset} = $self->get_subset();
  $args{directory} = File::Spec->catfile($directory, $self->get_dataset());
  $args{postal_code} //= get_postal_code_from_state($args{state});
  unless (-d $args{directory}){
    mkdir($args{directory}) or croak "Could not create subdirectory $args{directory}";
  }
  croak "No state specified" unless ($args{postal_code});
  unless ($args{sumlevel}){
    if ($args{level} && $level_key{$args{level}}){
      $args{sumlevel} = $level_key{$args{level}};
    }
  }
  $args{limits} //= {};
  if ($args{county}){
    if (ref($args{county})){
      croak "Invalid county" unless (ref($args{county}) eq "ARRAY");
      foreach my $county (@{$args{county}}){
	$args{limits}->{COUNTY}->{sprintf('%03d', $county)} = undef;
      }
    }
    else{
      $args{limits}->{COUNTY}->{sprintf('%03d', $args{county})} = undef;
    }
  }
  if ($args{zip}){
    if (ref($args{zip})){
      croak "Invalid zip" unless (ref($args{zip}) eq "ARRAY");
      foreach my $zip (@{$args{zip}}){
	$args{limits}->{ZCTA5}->{$zip} = undef;
      }
    }
    else{
      $args{limits}->{ZCTA5}->{$args{zip}} = undef;
    }
  }
  if ($args{county_sub}){
    if (ref($args{county_sub})){
      croak "Invalid county_sub" unless (ref($args{county_sub}) eq "ARRAY");
      foreach my $county_sub (@{$args{county_sub}}){
	$args{limits}->{COUSUB}->{sprintf('%05d', $county_sub)} = undef;
      }
    }
    else{
      $args{limits}->{COUSUB}->{sprintf('%05d', $args{county_sub})} = undef;
    }
  }
  return($dataset_dispatch{$self->get_dataset()}->($self, %args));
}

sub state_name{
  my %args = @_;
  croak "No postal code provided" unless ($args{postal_code});
  croak "Invalid postal code $args{postal_code}" unless ($state_from_postal_code{$args{postal_code}});
  my $name = $state_from_postal_code{$args{postal_code}}->[0];
  if ($args{postal_code} eq "US"){
    if ($args{dataset} eq "census_2010"){
      $name = "National";
    }
    elsif ($args{dataset} eq "census_2000" && $args{subset} eq "demographic_profile"){
      $name = "0 United States";
    }
    elsif ($args{dataset} eq "census_2000" && $args{subset} eq "sf1"){
      $name = "0Final_National";
    }
    elsif ($args{dataset} eq "census_2000" && $args{subset} eq "sf2"){
      $name = "0Final_National";
    }
    elsif ($args{dataset} eq "census_2000" && $args{subset} eq "sf3"){
      $name = "0_National";
    }
  }
  if ($args{of} && $args{of} eq "upper"){
    $name =~ s/ of / Of /;
  }
  if ($args{underscore}){
    $name =~ s/ /\_/g;
  }
  else{
    $name =~ s/ //g;
  }
  return($name);
}

sub get_postalcode {
  my $self = shift;
  my %args = @_;
  return ($args{postalcode}) if ($args{postalcode});
  return (get_postal_code_from_state($args{state}));
}

sub get_postal_code_from_state {
  my $state = shift;
  croak "No state provided" unless ($state);
  $state = uc($state);
  if (defined($fips_from_postal_code{$state})){
    return($state);
  }
  if ($state =~ /^[0-9]+$/){
    $state = int($state);
    if ($postal_code_from_fips{$state}){
      return($postal_code_from_fips{$state});
    }
  }
  if ($postal_code_from_state{$state}){
    return($postal_code_from_state{$state});
  }
  croak "Invalid state $state provided";
}

sub get_directory{
  return ($_[0]->{directory});
}

sub set_directory{
  $_[0]->{directory} = $_[1];
  unless (-d $_[0]->get_directory()){
    mkdir($_[0]->get_directory()) or croak "2514: Could not create directory " . $_[0]->get_directory();
    print STDERR "Creating directory " . $_[0]->get_directory() . "\n";
  }
  return;
}

sub get_dataset{
  return ($_[0]->{dataset});
}

sub set_dataset{
  $_[0]->{dataset} = corrected_dataset($_[1]);
  return;
}

sub get_subset{
  return ($_[0]->{subset} // 'only');
}

sub set_subset{
  $_[0]->{subset} = corrected_subset($_[1]);
  return;
}

sub list_of_states {
  my $self = shift;
  my %args = @_;
  my @return_array;
  foreach my $state (sort keys %state_from_postal_code){
    next if ($state_from_postal_code{$state}->[1] == 0);
    next if ($args{continental} && $state_from_postal_code{$state}->[2] == 0);
    push(@return_array, $state);
  }
  return(@return_array);
}

sub select_values_function {
  my $self = shift;
  my %args = @_;
  my $vals;
  if ($args{property} eq "state"){
    my $d = \%state_from_postal_code;
    foreach my $key (sort {lc($d->{$a}->[0]) cmp lc($d->{$b}->[0])} keys %{$d}){
      push(@{$vals}, [$d->{$key}->[0], {$args{property} => $d->{$key}->[0]}]);
    }
  }
  if ($args{property} eq "level"){
    my $d = \%sum_level_names;
    foreach my $value (sort values %{$d}){
      push(@{$vals}, [$value, {$args{property} => $value}]);
    }
  }
  if ($args{property} eq "boundaryYear"){
    foreach my $value (sort @possible_boundary_years){
      push(@{$vals}, [$value, {$args{property} => $value}]);
    }
  }
  if ($args{property} eq "dataset"){
    my $d = \%dataset_names;
    foreach my $value (sort values %{$d}){
      push(@{$vals}, [$value, {$args{property} => $value}]);
    }
  }
  if ($args{property} eq "subset"){
    my $d = $data_file_of{$self->get_dataset()};
    if ($d){
      foreach my $value (sort keys %{$d}){
	push(@{$vals}, [$value, {$args{property} => $value}]);
      }
    }
    else{
      $vals = [[-1, {$args{property} => "Not Necessary"}], ['n/a', {$args{property} => "[Close]"}]];
    }
  }
  # if ($args{property} eq "county"){
  #   push(@{$vals}, [undef, "[None]"]);
  #   foreach my $row (sort {$a->[1] cmp $b->[1]} @{$self->get_county_list(%args)}){
  #     push(@{$vals}, [$row->[1], {$args{property} => $row->[1]}]);
  #   }
  # }
  return($vals);
}

sub get_countycode {
  my $self = shift;
  my %args = @_;
  my %lookup = (map {$_->[1] => $_->[0], $_->[2] => $_->[0]} @{$self->get_county_list(%args)});
  my @inp;
  if (ref($args{county}) eq "ARRAY"){
    @inp = @{$args{county}};
  }
  else{
    @inp = ($args{county});
  }
  return(map{$lookup{$_}} @inp);
}

sub get_field_list {
  my $self = shift;
  my %args = @_;
  croak "No table id provided" unless ($args{table_id});
  my @vals;
  my $compartment = new Safe;
  my $acs = ($self->get_dataset() =~ /^acs/) ? 1 : 0;
  my $lookup_db_file = $self->get_lookup_file();
  #tableid|sequence|tabletitle|subjectarea|universe|definition
  my $dref = DBI->connect("dbi:SQLite:dbname=$lookup_db_file", "", "") or croak DBI->errstr;
  my $query_string = "select definition, universe from lookup where tableid=? order by subjectarea, tableid";
  my $query = $dref->prepare($query_string) or croak $dref->errstr;
  $query->execute($args{table_id}) or croak $query->errstr;
  while (my $d = $query->fetchrow_hashref()){
    my $aref = $compartment->reval($d->{definition});
    croak "Bad definition: $d->{definition}" unless ($aref);
    foreach my $d (@{$aref}){
      $d->[1] =~ s/^ +//;
      push(@vals, [$d->[0], $d->[1]]);
    }
  }
  $query->finish();
  $dref->disconnect();
  return(\@vals, $acs);
}

sub get_table_list {
  my $self = shift;
  my @vals;
  my $acs = ($self->get_dataset() =~ /^acs/) ? 1 : 0;
  my $lookup_db_file = $self->get_lookup_file();
  warn "Lookup db file is $lookup_db_file";
  #tableid|sequence|tabletitle|subjectarea|universe|definition
  my $dref = DBI->connect("dbi:SQLite:dbname=$lookup_db_file", "", "") or croak DBI->errstr;
  my $query_string = "select tabletitle, tableid, universe, subjectarea from lookup order by subjectarea, tableid";
  my $query = $dref->prepare($query_string) or croak $dref->errstr;
  $query->execute() or croak $query->errstr;
  while (my $aref = $query->fetchrow_arrayref()){
    push(@vals, [@{$aref}]);
  }
  $query->finish();
  $dref->disconnect();
  return(\@vals, $acs);
}

sub old_get_county_list {
  my $self = shift;
  my %args = @_;
  my @vals;
  my $acs = ($self->get_dataset() =~ /^acs/) ? 1 : 0;
  my $sumlevel = $self->get_sumlevel(%args);
  my $data_db_file = $self->get_data_file(%args);
  my $postal_code = $self->get_postalcode(%args);
  #warn "data file is $data_db_file";
  croak "Could not find data file" unless ($data_db_file);
  my $dref = DBI->connect("dbi:SQLite:dbname=$data_db_file", "", "") or croak DBI->errstr;
  my $string = "select COUNTY, NAME, GEOID from geo where " . ($acs ? "SUMLEVEL" : "SUMLEV") . "=? AND STUSAB=?";
  #warn "Query string is $string";
  my $query = $dref->prepare($string) or croak $dref->errstr;
  $query->execute('050', $postal_code) or croak $query->errstr;
  while (my $d = $query->fetchrow_hashref()){
    #warn "Found one value";
    push(@vals, [$d->{COUNTY}, $d->{NAME}, $d->{GEOID}]);
  }
  $query->finish();
  $dref->disconnect();
  return(\@vals);
}

1;
__END__

=head1 NAME

Census::US - Programmatically retrieve demogrphic and boundary information from the U.S. Census Bureau

=head1 VERSION

This document describes Census::US version 0.0.1


=head1 SYNOPSIS

    use Census::US;

=for author to fill in:
    Brief code example(s) here showing commonest usage(s).
    This section will be as far as many users bother reading
    so make it as educational and exeplary as possible.

=head1 DESCRIPTION

This module retrieves demographic information and boundary files from the United States Census Bureau's web site.  Demographic information is cached in Sqlite files to increase speed.

=head1 INTERFACE

=for author to fill in:
    Write a separate section listing the public components of the modules
    interface. These normally consist of either subroutines that may be
    exported, or methods that may be called on objects belonging to the
    classes provided by the module.


=head1 DIAGNOSTICS

=for author to fill in:
    List every single error and warning message that the module can
    generate (even the ones that will "never happen"), with a full
    explanation of each problem, one or more likely causes, and any
    suggested remedies.

=over

=item C<< Error message here, perhaps with %s placeholders >>

[Description of error here]

=item C<< Another error message here >>

[Description of error here]

[Et cetera, et cetera]

=back


=head1 CONFIGURATION AND ENVIRONMENT

=for author to fill in:
    A full explanation of any configuration system(s) used by the
    module, including the names and locations of any configuration
    files, and the meaning of any environment variables or properties
    that can be set. These descriptions must also include details of any
    configuration language used.
  
Census::US requires no configuration files or environment variables.


=head1 DEPENDENCIES

=for author to fill in:
    A list of all the other modules that this module relies upon,
    including any restrictions on versions, and an indication whether
    the module is part of the standard Perl distribution, part of the
    module's distribution, or must be installed separately. ]

None.


=head1 INCOMPATIBILITIES

=for author to fill in:
    A list of any modules that this module cannot be used in conjunction
    with. This may be due to name conflicts in the interface, or
    competition for system or program resources, or due to internal
    limitations of Perl (for example, many modules that use source code
    filters are mutually incompatible).

None reported.


=head1 BUGS AND LIMITATIONS

=for author to fill in:
    A list of known problems with the module, together with some
    indication Whether they are likely to be fixed in an upcoming
    release. Also a list of restrictions on the features the module
    does provide: data types that cannot be handled, performance issues
    and the circumstances in which they may arise, practical
    limitations on the size of data sets, special cases that are not
    (yet) handled, etc.

No bugs have been reported.

Please report any bugs or feature requests to
C<bug-census-us@rt.cpan.org>, or through the web interface at
L<http://rt.cpan.org>.


=head1 AUTHOR

Jonathan Pyle  C<< <jhpyle@gmail.com> >>


=head1 LICENCE AND COPYRIGHT

Copyright (c) 2013, Jonathan Pyle C<< <jhpyle@gmail.com> >>. All rights reserved.

This module is free software; you can redistribute it and/or
modify it under the same terms as Perl itself. See L<perlartistic>.


=head1 DISCLAIMER OF WARRANTY

BECAUSE THIS SOFTWARE IS LICENSED FREE OF CHARGE, THERE IS NO WARRANTY
FOR THE SOFTWARE, TO THE EXTENT PERMITTED BY APPLICABLE LAW. EXCEPT WHEN
OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES
PROVIDE THE SOFTWARE "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER
EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE
ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE SOFTWARE IS WITH
YOU. SHOULD THE SOFTWARE PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL
NECESSARY SERVICING, REPAIR, OR CORRECTION.

IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MAY MODIFY AND/OR
REDISTRIBUTE THE SOFTWARE AS PERMITTED BY THE ABOVE LICENCE, BE
LIABLE TO YOU FOR DAMAGES, INCLUDING ANY GENERAL, SPECIAL, INCIDENTAL,
OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OR INABILITY TO USE
THE SOFTWARE (INCLUDING BUT NOT LIMITED TO LOSS OF DATA OR DATA BEING
RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD PARTIES OR A
FAILURE OF THE SOFTWARE TO OPERATE WITH ANY OTHER SOFTWARE), EVEN IF
SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF
SUCH DAMAGES.

v.in.ogr dsn=. layer=gz_2010_us_050_00_500k output=counties location=us where="not (GEO_ID like '%US02%' or GEO_ID like '%US15%' or GEO_ID like '%US72%')"
echo "select * from counties where (GEO_ID like '%US02%' or GEO_ID like '%US15%' or GEO_ID like '%US72%')" | db.select
v.db.addcol map=counties columns="GRASSRGB varchar(11)"
d.mon x0
d.vect map=counties type=boundary

# if (0){
#   my $R = Statistics::R->new();
#   my @vals;
#   foreach my $foo (1..100){
#     push(@vals, rand(10));
#   }
#   $R->set('vals', \@vals);
#   $R->run('mymedian <- median(vals)');
#   my $output = $R->get('mymedian');
#   print "$output\n";
#   $R->stop();
#   exit;
# }

# if (0){
#   my $kml_file = "/home/jpyle/.census-us/shapefiles/US/my.kml";
#   my $twig = XML::Twig->new
#     (
#      twig_handlers =>
#      {
#       Placemark => sub {
# 	my $placemark = $_;
# 	my %result;
# 	#print "Found a placemark called " . $placemark->first_child('name')->text() . "\n";
# 	my $schemadata = $placemark->first_child('ExtendedData')->first_child('SchemaData');
# 	$result{url} = $schemadata->att('schemaUrl');
# 	foreach my $dataitem ($schemadata->children('SimpleData')){
# 	  $result{$dataitem->att('name')} = $dataitem->text();
# 	}
# 	foreach my $polygon ($placemark->children('Polygon')){
# 	  $result{polygon} .= $polygon->sprint();
# 	}
# 	print Dumper(\%result) . "\n";
# 	exit;
#       },
#      },
#      pretty_print => 'none',
#      empty_tags => 'html',
#     );
#   $twig->parsefile($kml_file);
#   $twig->flush();
#   exit;
# }

# if (0){
#   my $zip_file = "/home/jpyle/.census-us/shapefiles/US/gz_2010_us_050_00_500k.zip";
#   my $zip_dest = $zip_file;
#   $zip_dest =~ s/(.*)\/.*/$1\//;
#   my $zip = Archive::Zip->new();
#   print "zip file $zip_file\nzip dest $zip_dest\n";
#   croak "Could not read zip file $zip_file" unless ( $zip->read( $zip_file ) == AZ_OK );
#   croak "Could not extract files" unless ( $zip->extractTree(undef, $zip_dest) == AZ_OK );
#   #unlink($zip_file);

#   my $shape_file_base = $zip_file;
#   $shape_file_base =~ s/\.zip$//i;
#   my $shapefile = new Geo::ShapeFile($shape_file_base);
#   foreach my $n (1 .. $shapefile->shapes()) {
#     my %db = $shapefile->get_dbf_record($n);
#     next unless ($db{STATE} == 42);
#     print Dumper(\%db);
#   }
#   exit;
# }
