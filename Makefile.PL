use strict;
use warnings;
use ExtUtils::MakeMaker;
use ExtUtils::Manifest;

ExtUtils::Manifest::mkmanifest();

WriteMakefile
  (
   NAME                => 'Census::US',
   AUTHOR              => 'Jonathan Pyle <jpyle@litigationdatabase.org>',
   VERSION_FROM        => 'lib/Census/US.pm',
   ABSTRACT_FROM       => 'lib/Census/US.pm',
   PL_FILES            => {},
   EXE_FILES	       => [],
   PREREQ_PM           => {
			   'Archive::Zip' => 0,
			   'DBI' => 0,
			   'Data::Dumper' => 0,
			   'File::Basename' => 0,
			   'File::Copy' => 0,
			   'File::Spec' => 0,
			   'IO::File' => 0,
			   'LWP::UserAgent' => 0,
			   'Safe' => 0,
			   'Text::CSV_XS' => 0,
			   'XML::Twig' => 0,
			  },
   dist                => { COMPRESS => 'gzip -9f', SUFFIX => 'gz', },
   clean               => { FILES => 'Census-US-* MANIFEST MANIFEST.bak' },
  );
